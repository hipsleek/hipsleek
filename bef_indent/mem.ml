#include "xdebug.cppo"
open VarGen
(* asankhs:  Created on 03-Sep-2012 for Memory Specifications *)
(* Uses Field Annotations (Immutable) and Bag Constraints (Mona), run with --mem --field-ann -tp om *)
(* For Ramifications use --ramify it will turn off unfold of duplicated pointers in solver.ml which is required to do ramifications *)

open Globals
open Gen.Basic
open Gen.BList
open Label_only
open Cprinter

module CF = Cformula
module CP = Cpure
module IP = Ipure
module MCP = Mcpure
module Err = Error
module IF = Iformula
module I = Iast
module C = Cast
module Imm = Immutable
module TP = Tpdispatcher

let mk_mem_perm_formula 
(mem_exp: CP.exp) (isexact: bool) (fv: (ident * (CP.exp list)) list) (fl: (ident * (CP.ann list)) list) (g: CP.formula list)
: CF.mem_perm_formula = 
	{ CF.mem_formula_exp = mem_exp;
	  CF.mem_formula_exact = isexact;
      CF.mem_formula_field_values = fv;
	  CF.mem_formula_field_layout = fl;
	  CF.mem_formula_guards = g;}

let rec intersect_list_val (ann_lst_l: CP.exp list) (ann_lst_r: CP.exp list): CP.exp list =
  match (ann_lst_l, ann_lst_r) with
    | ([], []) -> []
    | (ann_l :: tl, ann_r :: tr ) ->
        begin
        match ann_l,ann_r with
          | CP.Var(sv1,_),CP.Var(sv2,_) ->
              if CP.is_anon_var sv1 || CP.eq_spec_var sv1 sv2 then ann_l :: (intersect_list_val tl tr)
              else if CP.is_anon_var sv2 then ann_r :: (intersect_list_val tl tr)
              else Err.report_error {Err.error_loc = no_pos;
			                         Err.error_text = "[mem.ml] : Memory Spec field values are different vars";}
          | CP.IConst(i1,_),CP.IConst(i2,_) -> 
              if i1 == i2 then ann_l ::(intersect_list_val tl tr)
              else Err.report_error {Err.error_loc = no_pos;
			                         Err.error_text = "[mem.ml] : Memory Spec field values are different ints";}
          | CP.IConst(i,_),CP.Var(sv,_) -> 
              if CP.is_anon_var sv then ann_r ::(intersect_list_val tl tr)
              else Err.report_error {Err.error_loc = no_pos;
			                         Err.error_text = "[mem.ml] : Memory Spec field values are inconsistent int and var";}
          | CP.Var(sv,_),CP.IConst(i,_) -> 
              if CP.is_anon_var sv then ann_l ::(intersect_list_val tl tr)
              else Err.report_error {Err.error_loc = no_pos;
			                         Err.error_text = "[mem.ml] : Memory Spec field values are inconsistent var and int";}
          | _,_ -> Err.report_error {Err.error_loc = no_pos;
			                         Err.error_text = "[mem.ml] : Memory Spec field values are inconsistent types";}
      end
    | (_, _) -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Spec should have same number of fields values";}

let rec intersect_list_ann_no_inter (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list): CP.ann list =
  match (ann_lst_l, ann_lst_r) with
    | ([], []) -> []
    | (ann_l :: tl, ann_r :: tr ) ->
      begin
	match ann_l, ann_r with 
	  | CP.ConstAnn(Mutable), CP.ConstAnn(Accs)
  	  | CP.ConstAnn(Imm), CP.ConstAnn(Accs) 
  	  | CP.ConstAnn(Lend), CP.ConstAnn(Accs)
	  | CP.ConstAnn(Lend), CP.ConstAnn(Lend) -> ann_l :: (intersect_list_ann_no_inter tl tr)	
  	  | CP.ConstAnn(Accs), CP.ConstAnn(Mutable)
  	  | CP.ConstAnn(Accs), CP.ConstAnn(Imm)
	  | CP.ConstAnn(Accs), CP.ConstAnn(Lend) 
  	  | CP.ConstAnn(Accs), CP.ConstAnn(Accs)-> ann_r :: (intersect_list_ann_no_inter tl tr)
  	  | _ , _ -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Spec field layouts may interfere";}

      end
    | (_, _) -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Spec should have same number of fields in layout";}

let rec intersect_list_ann (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list): CP.ann list =
  match (ann_lst_l, ann_lst_r) with
    | ([], []) -> []
    | (ann_l :: tl, ann_r :: tr ) ->
      begin
	match ann_r with 
	  | CP.ConstAnn(Mutable) -> ann_r :: (intersect_list_ann tl tr)		   
	  | CP.ConstAnn(Imm)     -> if (CP.isMutable ann_l) then ann_l :: (intersect_list_ann tl tr)
	  			 else ann_r :: (intersect_list_ann tl tr)
	  | CP.ConstAnn(Lend)    -> if (CP.isAccs ann_l) then ann_r :: (intersect_list_ann tl tr)
	  			 else ann_l :: (intersect_list_ann tl tr)
	  | CP.TempAnn _ | CP.NoAnn
	  | CP.TempRes _
	  | CP.ConstAnn(Accs)    -> ann_l :: (intersect_list_ann tl tr)
	  | CP.PolyAnn(v)        -> ann_l :: (intersect_list_ann tl tr) (* TODO(ann): check if var ann is replaced or not *)
      end
    | (_, _) -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Spec should have same number of fields in layout";}

let mem_guards_checking (fl1 : CP.formula) (fl2: CP.formula list) pos =
	let flag = List.exists (fun x -> let r,_,_  = x_add TP.imply_one 6 fl1 x "mem_guard_imply" false None in r) fl2 in
	if flag then ()   
	else 
	(*if CP.isConstTrue fl1 then ()
	else*)
	Err.report_error { Err.error_loc = pos;
	Err.error_text = "[mem.ml] : Memory Spec Guards fail during implication checking";}
	
let mem_guards_checking_reverse (fl1: CP.formula list) (fl2 : CP.formula) pos = 
	let flag = List.exists (fun x ->  
	let x_fvs = CP.fv x in
	let relevant_slice = CP.join_conjunctions (List.filter 
		(fun c -> if (CP.disjoint x_fvs (CP.fv c)) then false else true)
		(CP.split_conjunctions fl2)) in
    let sat_subno = ref 0 in
    let f = CP.mkAnd x relevant_slice no_pos in TP.is_sat_sub_no 100 f sat_subno) fl1 in
	if flag then ()   
	else 
	Err.report_error { Err.error_loc = pos;
	Err.error_text = "[mem.ml] : Memory Spec Guards fail during reverse sat checking";}	
		    
let rec fl_subtyping (fl1 : (ident * (CP.ann list)) list) (fl2: (ident * (CP.ann list)) list) pos =
  (*let () = print_string("\n\nfl1: ") in 
  let todo_unk = List.map (fun c -> 
    let () = print_string ((fst c)^" : "^(String.concat "," (List.map string_of_imm (snd c)))^" ") in c) fl1 in
  let () = print_string("\nfl2: ") in 
  let todo_unk = List.map (fun c -> 
    let () = print_string ((fst c)^" : "^(String.concat "," (List.map string_of_imm (snd c)))^" ") in c) fl2 in *)
	match fl1 with
	| [] -> ()
	| x::xs -> let matched_fields = List.filter (fun c -> if (String.compare (fst c) (fst x)) == 0 then true else false) fl2
		    (*in let todo_unk = List.map
		    (fun c -> let () = print_string (String.concat "," (List.map string_of_imm (snd c))) in c) fl2*)
		    in (*let todo_unk = List.map
		    (fun c -> let () = print_string ("fl2: "^(String.concat "," (List.map string_of_imm (snd c)))^"\n") in c) fl2
		    in*) let tmp = (List.exists (fun c -> let b,_,_ ,_= (Imm.subtype_ann_list [] [] (snd x) (snd c)) in 
     	    (*let () = 
		    print_string ("Ann Lists: "^ (*(string_of_bool b) ^*)(String.concat "," (List.map string_of_imm (snd c)))^" :> "^
		    		(String.concat "," (List.map string_of_imm (snd x)))^ "\n")
		    in*)
		    b) matched_fields)
		    in (*let () = print_string ((string_of_bool tmp)^"\n") 
		    in*)  let () = if (tmp || List.length matched_fields == 0) then () else 
			Err.report_error { Err.error_loc = pos;
			Err.error_text = "[mem.ml] : Memory Spec field layout doesn't respect annotation subtyping";}
		    in fl_subtyping xs fl2 pos

let rec fl_subtyping_rev (fl1 : (ident * (CP.ann list)) list) (fl2: (ident * (CP.ann list)) list)  pos =
  let helper fl1 fl2 pos = 
  (* fl2 will be a list of 1 value for this case *)
  if List.length fl2 > 1 then Err.report_error { Err.error_loc = pos;
			Err.error_text = "[mem.ml] : Memory Spec field layout has more number of layouts than expected (1)";}
  else if List.length fl2 == 0 then () else
  let matched_fields = List.filter (fun c -> if (String.compare (fst c) (fst (List.hd fl2))) == 0 then true else false) fl1 in 
  if List.length matched_fields == 0 then  Err.report_error { Err.error_loc = pos;
			Err.error_text = "[mem.ml] : Memory Spec field layout doesn't have a matching field";}
  else let tmp = 
         List.exists (fun c -> let b,_,_, _ = (Imm.subtype_ann_list [] [] (snd c) (snd (List.hd matched_fields))) in b ) fl1 in
       if  tmp then () else Err.report_error { Err.error_loc = pos;
			Err.error_text = "[mem.ml] : Memory Spec field layout doesn't respect annotation subtyping";}
  in match fl2 with
    | [] -> ()
    | x::xs -> let () = helper fl1 [x] pos in fl_subtyping_rev fl1 xs pos

let rec fv_match (fv1 : (ident * (CP.exp list)) list) (fv2: (ident * (CP.exp list)) list) pos =
  (*let () = print_string("\n\nfl1: ") in 
  let todo_unk = List.map (fun c -> 
    let () = print_string ((fst c)^" : "^(String.concat "," (List.map string_of_imm (snd c)))^" ") in c) fl1 in
  let () = print_string("\nfl2: ") in 
  let todo_unk = List.map (fun c -> 
    let () = print_string ((fst c)^" : "^(String.concat "," (List.map string_of_imm (snd c)))^" ") in c) fl2 in *)
  let rec helper f1 f2 =
    match (f1, f2) with
    | ([], []) -> true
    | (vl :: tl, vr :: tr ) -> 
        (match vl,vr with
          | _ , CP.Var(sv,_)
          | CP.Var(sv,_), _ -> if CP.is_anon_var sv then true && helper tl tr else false
          | _  , _-> if CP.eq_exp_no_aset vl vr then true && helper tl tr else false)
    | (_, _) -> false
  in 
	match fv1 with
	| [] -> ()
	| x::xs -> let matched_fields = List.filter (fun c -> if (String.compare (fst c) (fst x)) == 0 then true else false) fv2
		    in (*let todo_unk = List.map
		    (fun c -> let () = print_string ("fl2: "^(String.concat "," (List.map string_of_imm (snd c)))^"\n") in c) fl2
		    in let todo_unk = List.map
		    (fun c -> let () = print_string ("fl1: "^(String.concat "," (List.map string_of_imm (snd c)))^"\n") in c) fl1
		    in *)let tmp = (List.for_all (fun c -> helper (snd x) (snd c))
     	    (*let () = 
		    print_string ("Ann Lists: "^ (*(string_of_bool b) ^*)(String.concat "," (List.map string_of_imm (snd c)))^" :> "^
		    		(String.concat "," (List.map string_of_imm (snd x)))^ "\n")
		    in*)
		    matched_fields)
		    in (*let () = print_string ((string_of_bool tmp)^"\n") 
		    in*)  let () = if (tmp || List.length matched_fields == 0) then () else 
			Err.report_error { Err.error_loc = pos;
			Err.error_text = "[mem.ml] : Memory Spec field values don't match";}
		    in fv_match xs fv2 pos

let rec fv_intersect_no_inter (fl1 : (ident * (CP.exp list)) list) (fl2: (ident * (CP.exp list)) list) 
: (ident * (CP.exp list)) list =
	match fl2 with
	| [] -> fl1
	| x::xs -> let (todo_unk) = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then (fst c), intersect_list_val (snd c) (snd x) 
				else c) fl1 in fv_intersect_no_inter fl1 xs
				
let rec fv_intersect (fl1 : (ident * (CP.exp list)) list) (fl2: (ident * (CP.exp list)) list) 
: (ident * (CP.exp list)) list =
	match fl2 with
	| [] -> fl1
	| x::xs -> let (todo_unk) = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then (fst c), intersect_list_val (snd c) (snd x) 
				else c) fl1 in fv_intersect fl1 xs				
				
let rec fv_diff (fl1 : (ident * (CP.exp list)) list) (fl2: (ident * (CP.exp list)) list) 
: (ident * (CP.exp list)) list =
	match fl2 with
	| [] -> fl1
	| x::xs -> let todo_unk = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then (fst c),intersect_list_val (snd c) (snd x) 
				else c) fl1 in fv_diff fl1 xs

let rec fl_intersect_no_inter (fl1 : (ident * (CP.ann list)) list) (fl2: (ident * (CP.ann list)) list) : (ident * (CP.ann list)) list =
	match fl2 with
	| [] -> fl1
	| x::xs -> let todo_unk = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then (fst c), intersect_list_ann_no_inter (snd c) (snd x) 
				else c) fl1 in fl_intersect_no_inter fl1 xs
				
let rec fl_intersect (fl1 : (ident * (CP.ann list)) list) (fl2: (ident * (CP.ann list)) list) : (ident * (CP.ann list)) list =
	match fl2 with
	| [] -> fl1
	| x::xs -> let todo_unk = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then (fst c), intersect_list_ann (snd c) (snd x) 
				else c) fl1 in fl_intersect fl1 xs				
				
let rec fl_diff (fl1 : (ident * (CP.ann list)) list) (fl2: (ident * (CP.ann list)) list) : (ident * (CP.ann list)) list =
	match fl2 with
	| [] -> fl1
	| x::xs -> let todo_unk = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then 
                                  let (an,_), _, _ = Imm.replace_list_ann_mem (snd c) (snd x) [] [][] in
                                  (fst c),an
				else c) fl1 in fl_diff fl1 xs

let get_field_name (fl : (ident * (CP.ann list)) list) : ident = 
	try fst (List.hd fl)
	with | _ -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Empty Field Layout";}

let rec make_disj_constraints (exps: CP.exp list) (mpf : CF.mem_perm_formula) : CP.formula =
	match exps with
	| [] -> CP.mkTrue no_pos
	| x::xs -> match x with
		   | CP.Var(sv,pos) -> let svisin = CP.BForm((CP.BagNotIn(sv,mpf.CF.mem_formula_exp,pos),None),None)
		   			in (CP.mkAnd svisin (make_disj_constraints xs mpf)  pos)
		   | _ -> CP.mkTrue no_pos
				
let mem_disj_union (f1:CF.mem_perm_formula) (f2:CF.mem_perm_formula) : CF.mem_perm_formula * CP.formula = 
	let pos = CP.pos_of_exp f1.CF.mem_formula_exp in
	let mpf = {CF.mem_formula_exp = CP.BagUnion(f1.CF.mem_formula_exp::[f2.CF.mem_formula_exp],pos);
		CF.mem_formula_exact = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact then true else false;
                CF.mem_formula_field_values = remove_dups f1.CF.mem_formula_field_values@f2.CF.mem_formula_field_values;
		CF.mem_formula_field_layout = remove_dups f1.CF.mem_formula_field_layout@f2.CF.mem_formula_field_layout;
		CF.mem_formula_guards = remove_dups f1.CF.mem_formula_guards@f2.CF.mem_formula_guards;}
		in
	(*let tmp_var = CP.SpecVar((Named (get_field_name mfp.CF.mem_formula_field_layout)),"Anon"^(fresh_trailer()),Unprimed) in
	let df1 = CP.BForm((CP.BagNotIn(tmp_var,f1.CF.mem_formula_exp,pos),None),None) in
	let df2 = CP.BForm((CP.BagNotIn(tmp_var,f2.CF.mem_formula_exp,pos),None),None) in
	let disj_formula = (CP.mkOr  df1 df2 None pos) in
	let cf = CP.mkForall [tmp_var] disj_formula None pos in*)
	match f1.CF.mem_formula_exp, f2.CF.mem_formula_exp with
	| CP.Bag(exp1,pos1) , CP.Bag(exp2,pos2) -> let cf1 = make_disj_constraints exp1 f2 in
						let cf2 = make_disj_constraints exp2 f1 in
						let cf = CP.mkAnd cf1 cf2 pos1 in
						mpf,cf
	| CP.Bag(exp1,pos1) , _ -> let cf1 = make_disj_constraints exp1 f2 in mpf,cf1
	| _ , CP.Bag(exp2,pos2) -> let cf2 = make_disj_constraints exp2 f1 in mpf,cf2	       
	| _ , _ -> (*let cf = CP.mkNeq (CP.BagIntersect(f1.CF.mem_formula_exp::[f2.CF.mem_formula_exp],pos)) (CP.Bag([],no_pos)) pos in
	       let cf = CP.BForm((cf,None),None) in *)
	       let cf = CP.mkTrue no_pos in 
	       mpf,cf

let mem_union (f1:CF.mem_perm_formula) (f2:CF.mem_perm_formula) : CF.mem_perm_formula = 
	let pos = CP.pos_of_exp f1.CF.mem_formula_exp in
		{CF.mem_formula_exp = CP.BagUnion(f1.CF.mem_formula_exp::[f2.CF.mem_formula_exp],pos);
		CF.mem_formula_exact = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact then true else false;
		CF.mem_formula_field_layout = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact 
					then (fl_intersect_no_inter f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout)
					else (fl_intersect f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout);
                CF.mem_formula_field_values =  if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact 
					then (fv_intersect_no_inter f1.CF.mem_formula_field_values f2.CF.mem_formula_field_values)
					else (fv_intersect f1.CF.mem_formula_field_values f2.CF.mem_formula_field_values);
		CF.mem_formula_guards = remove_dups f1.CF.mem_formula_guards@f2.CF.mem_formula_guards;}
		(*remove_dups f1.CF.mem_formula_field_layout@f2.CF.mem_formula_field_layout;}*)

let mem_intersect (f1:CF.mem_perm_formula) (f2:CF.mem_perm_formula) : CF.mem_perm_formula =
	let pos = CP.pos_of_exp f1.CF.mem_formula_exp in
		{CF.mem_formula_exp = CP.BagIntersect(f1.CF.mem_formula_exp::[f2.CF.mem_formula_exp],pos);
		CF.mem_formula_exact = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact then true else false;
		CF.mem_formula_field_layout = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact 
					then (fl_intersect_no_inter f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout)
					else (fl_intersect f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout);
                CF.mem_formula_field_values =  if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact 
					then (fv_intersect_no_inter f1.CF.mem_formula_field_values f2.CF.mem_formula_field_values)
					else (fv_intersect f1.CF.mem_formula_field_values f2.CF.mem_formula_field_values);
		CF.mem_formula_guards = remove_dups f1.CF.mem_formula_guards@f2.CF.mem_formula_guards;}
		
let mem_diff (f1:CF.mem_perm_formula) (f2:CF.mem_perm_formula) : CF.mem_perm_formula =
	let pos = CP.pos_of_exp f1.CF.mem_formula_exp in
		{CF.mem_formula_exp = CP.BagDiff(f1.CF.mem_formula_exp,f2.CF.mem_formula_exp,pos);
		CF.mem_formula_exact = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact then true else false;
		CF.mem_formula_field_layout = (fl_diff f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout);
		CF.mem_formula_field_values = (fv_diff f1.CF.mem_formula_field_values f2.CF.mem_formula_field_values);
		CF.mem_formula_guards = remove_dups f1.CF.mem_formula_guards@f2.CF.mem_formula_guards;}

let rec xmem_heap (f: CF.h_formula) (vl: C.view_decl list) : CF.mem_perm_formula * CP.formula list = 
	match f with
	| CF.Star ({ CF.h_formula_star_h1 = f1;
		     CF.h_formula_star_h2 = f2;
		     CF.h_formula_star_pos = pos;}) -> 
		     let mpf1,disjf1 = xmem_heap f1 vl in
		     let mpf2,disjf2 = xmem_heap f2 vl in
		     let mpf,disj = mem_disj_union mpf1 mpf2 in
		     mpf, disj::disjf1 @ disjf2  
	| CF.StarMinus ({ CF.h_formula_starminus_h1 = f1;
		     CF.h_formula_starminus_h2 = f2;
		     CF.h_formula_starminus_pos = pos;}) -> 
		     let mpf1,disjf1 = xmem_heap f1 vl in
		     let mpf2,disjf2 = xmem_heap f2 vl in
		     let mpf = mem_diff mpf1 mpf2 in
		     mpf, disjf1 @ disjf2  		     
	| CF.Conj ({ CF.h_formula_conj_h1 = f1;
		     CF.h_formula_conj_h2 = f2;
		     CF.h_formula_conj_pos = pos;}) ->
		     let mpf1,disjf1 = xmem_heap f1 vl in
		     let mpf2,disjf2 = xmem_heap f2 vl in
		     let mpf = mem_union mpf1 mpf2 in
		     mpf, disjf1@disjf2
	| CF.ConjStar ({ CF.h_formula_conjstar_h1 = f1;
		     CF.h_formula_conjstar_h2 = f2;
		     CF.h_formula_conjstar_pos = pos;}) ->
		     let mpf1,disjf1 = xmem_heap f1 vl in
		     let mpf2,disjf2 = xmem_heap f2 vl in
		     let mpf = mem_union mpf1 mpf2 in
		     mpf, disjf1@disjf2  
	| CF.ConjConj ({ CF.h_formula_conjconj_h1 = f1;
		     CF.h_formula_conjconj_h2 = f2;
		     CF.h_formula_conjconj_pos = pos;}) ->
		     let mpf1,disjf1 = xmem_heap f1 vl in
		     let mpf2,disjf2 = xmem_heap f2 vl in
		     let mpf = mem_union mpf1 mpf2 in
		     mpf, disjf1@disjf2  		     		       
	| CF.Phase ({ CF.h_formula_phase_rd = f1;
		      CF.h_formula_phase_rw = f2;
		      CF.h_formula_phase_pos = pos;}) -> 
		      let mpf1,disjf1 = xmem_heap f1 vl in
		      let mpf2,disjf2 = xmem_heap f2 vl in
		      let mpf = mem_union mpf1 mpf2 in
		      mpf, disjf1@disjf2
	| CF.ThreadNode ({ CF.h_formula_thread_node = dn;
			 CF.h_formula_thread_name = name;
			 CF.h_formula_thread_pos = pos;}) -> 
        (*TOCHECK: currently ignore delayed & resource*)
		 (mk_mem_perm_formula (CP.Bag([CP.Var(dn,no_pos)],pos)) true [(name,[])] [(name, [])] []), []

	| CF.DataNode ({ CF.h_formula_data_node = dn;
			 CF.h_formula_data_name = name;
			 CF.h_formula_data_param_imm = fl;
             CF.h_formula_data_arguments = da;
			 CF.h_formula_data_pos = pos;}) -> 
         let fv = List.map 
           (fun c -> if CP.is_const c then CP.Var(c,pos)  
                     else CP.Var(CP.SpecVar(Int,"Anon_"^(fresh_trailer()),Unprimed),pos)) da in
		 (mk_mem_perm_formula (CP.Bag([CP.Var(dn,no_pos)],pos)) true [(name,fv)] [(name, fl)] []), []
	| CF.ViewNode ({ CF.h_formula_view_node = vn;
			 CF.h_formula_view_name = name;
			 CF.h_formula_view_arguments = argl;
			 CF.h_formula_view_pos = pos;}) -> 
			 	(*let new_var = CP.Var(CP.SpecVar((BagT (Named name)),"Anon"^(fresh_trailer()),Unprimed),pos) in 
			 	mk_mem_perm_formula (CP.Bag([new_var],pos)) false []*)
			 	let vdef = x_add C.look_up_view_def_raw 20 vl name in
			 	let mpf = vdef.C.view_mem in
			 	(match mpf with
				| Some mpf -> 
				 	let mexp = mpf.CF.mem_formula_exp in
				 	let gforms = mpf.CF.mem_formula_guards in
                                        (*let fv = mpf.CF.mem_formula_field_values in*) 
				 	(*let () = print_string("Free Var in Mem Spec :" ^ 
				 	(String.concat "," (List.map string_of_spec_var (CP.afv mexp))) ^"\n") in
				 	let () = print_string("Arg List :" ^ 
				 	(String.concat "," (List.map string_of_spec_var argl)) ^"\n") in*)
				 	let sbst_self = (*mexp in*)
		 	CP.e_apply_subs (List.combine [Cpure.SpecVar ((Named vdef.C.view_data_name), self, Unprimed)] [vn]) mexp in
				 	let new_mem_exp = CP.e_apply_subs (List.combine vdef.C.view_vars argl) sbst_self in
				 	(*let () = print_string("Bag Exp :" ^ (string_of_formula_exp new_mem_exp) ^"\n") in*)
			 	        (*mk_mem_perm_formula new_mem_exp mpf.CF.mem_formula_exact mpf.CF.mem_formula_field_layout*)
			 	        (mk_mem_perm_formula new_mem_exp mpf.CF.mem_formula_exact [] [] gforms), []
			 	| None -> (mk_mem_perm_formula (CP.Bag([],no_pos)) false [] [] []),[] )
  	| CF.Hole _ | CF.FrmHole _ | CF.HEmp | CF.HVar _ | CF.HFalse | CF.HTrue | CF.HRel _ -> (mk_mem_perm_formula (CP.Bag([],no_pos)) false [] [] []),[]

let rec xmem (f: CF.formula) (vl:C.view_decl list) (me: CF.mem_perm_formula): MCP.mix_formula =
	match f with
	| CF.Or ({CF.formula_or_f1 = f1;
		CF.formula_or_f2 = f2;
		CF.formula_or_pos = pos;}) -> (*MCP.mkOr_mems (xmem f1 vl me) (xmem f2 vl me) *)
						MCP.merge_mems (xmem f1 vl me) (xmem f2 vl me) true
	| CF.Base ({ CF.formula_base_heap = f;
	          CF.formula_base_pure = p;
		  CF.formula_base_pos = pos;}) -> 
		  let mpform,disjform = (xmem_heap f vl) in
         	  let mfe1 = me.CF.mem_formula_exp in
		  let mfe2 = mpform.CF.mem_formula_exp in
		  let f1 = CP.BForm((CP.BagSub(mfe1,mfe2,pos),None),None) in
		  let () = fl_subtyping mpform.CF.mem_formula_field_layout me.CF.mem_formula_field_layout pos in
          let () = fv_match mpform.CF.mem_formula_field_values me.CF.mem_formula_field_values pos in
		  let () = if (CF.is_empty_heap f) then ()
		  	  else mem_guards_checking (MCP.pure_of_mix p) me.CF.mem_formula_guards pos in 
		  let f = if me.CF.mem_formula_exact 
		  	  then let f2 = CP.BForm((CP.BagSub(mfe2,mfe1,pos),None),None)
		  		in let () = fl_subtyping_rev me.CF.mem_formula_field_layout mpform.CF.mem_formula_field_layout pos in
		  		let () =  if (CF.is_empty_heap f) then ()
					 else mem_guards_checking_reverse me.CF.mem_formula_guards (MCP.pure_of_mix p) pos
		  		in MCP.merge_mems (MCP.mix_of_pure f1) (MCP.mix_of_pure f2) true
		  	  else MCP.mix_of_pure f1 
		  in (List.fold_left (fun a b -> MCP.merge_mems a (MCP.mix_of_pure b) true) f disjform)
	| CF.Exists ({ CF.formula_exists_qvars = qvars;
		    CF.formula_exists_heap = f;
     	            CF.formula_exists_pure = p;
		    CF.formula_exists_pos = pos;}) -> 
		    let mpform,disjform = (xmem_heap f vl) in
		    let mfe1 = me.CF.mem_formula_exp in
		    let mfe2 = mpform.CF.mem_formula_exp in
		    let f1 = CP.BForm((CP.BagSub(mfe1,mfe2,pos),None),None) in
		    let () = fl_subtyping mpform.CF.mem_formula_field_layout me.CF.mem_formula_field_layout pos in
            let () = fv_match mpform.CF.mem_formula_field_values me.CF.mem_formula_field_values pos in
      		    let () = if (CF.is_empty_heap f) then ()
		    	    else mem_guards_checking (MCP.pure_of_mix p) me.CF.mem_formula_guards pos in 
		    let f = if me.CF.mem_formula_exact 
		            then let f2 = CP.BForm((CP.BagSub(mfe2,mfe1,pos),None),None)
		    		 in let () = fl_subtyping_rev me.CF.mem_formula_field_layout mpform.CF.mem_formula_field_layout pos in
		    		 let () = if (CF.is_empty_heap f) then ()
		    			 else mem_guards_checking_reverse me.CF.mem_formula_guards (MCP.pure_of_mix p) pos
				 in let fe = MCP.merge_mems (MCP.mix_of_pure f1) (MCP.mix_of_pure f2) true
				 (*in MCP.memo_pure_push_exists qvars fe*)
				 in fe
		    		 else (MCP.mix_of_pure f1)
		    		      (*MCP.memo_pure_push_exists qvars (MCP.mix_of_pure f1)*)
       	    in MCP.memo_pure_push_exists qvars (List.fold_left (fun a b -> MCP.merge_mems a (MCP.mix_of_pure b) true) f disjform)

let xmem_perm (f: CF.formula) (vl:C.view_decl list) : CF.mem_perm_formula * MCP.mix_formula * CP.spec_var list =
	let mix_true = MCP.mix_of_pure (CP.mkTrue no_pos) in 
	match f with
	| CF.Or ({CF.formula_or_f1 = f1;
		CF.formula_or_f2 = f2;
		CF.formula_or_pos = pos;}) -> (* Do not call with disjunctive formula*)
					      (mk_mem_perm_formula (CP.Bag([],no_pos)) false [] [] []),mix_true,[]
	| CF.Base ({ CF.formula_base_heap = f;
		  CF.formula_base_pos = pos;}) -> 
		  let mpform,disjform = (xmem_heap f vl) 
		  in mpform,(List.fold_left (fun a b -> MCP.merge_mems a (MCP.mix_of_pure b) true) mix_true disjform),[]
	| CF.Exists ({ CF.formula_exists_qvars = qvars;
		    CF.formula_exists_heap = f;
		    CF.formula_exists_pos = pos;}) -> 
		    let mpform,disjform = (xmem_heap f vl) in
		    let pureform = (List.fold_left (fun a b -> MCP.merge_mems a (MCP.mix_of_pure b) true) mix_true disjform) 			    in mpform, pureform, qvars

let entail_mem_perm_formula (ante: CF.formula) (conseq: CF.formula) (vl: C.view_decl list) pos : MCP.mix_formula = 
	let ante_mem,ante_mem_pure,ante_qvars = xmem_perm ante vl in
	let conseq_mem,conseq_mem_pure,conseq_qvars = xmem_perm conseq vl in
	let mfe_ante = ante_mem.CF.mem_formula_exp in
	let mfe_conseq = conseq_mem.CF.mem_formula_exp in
	let subset_formula = CP.BForm((CP.BagSub(mfe_conseq,mfe_ante,pos),None),None) in
	let () = fl_subtyping ante_mem.CF.mem_formula_field_layout conseq_mem.CF.mem_formula_field_layout pos in
	let pure_formulas = MCP.merge_mems ante_mem_pure conseq_mem_pure true in
	MCP.memo_pure_push_exists (ante_qvars@conseq_qvars) (MCP.merge_mems (MCP.mix_of_pure subset_formula) pure_formulas true)
	       	    
let get_data_fields (ddn : (ident * ((I.typed_ident * loc * bool) list)) list)  (name : ident) : ((I.typed_ident * loc * bool) list) = 
	try (snd (List.find (fun c -> (*let () = print_string(" DD: "^(fst c)^ "N: "^name) in  *)
	if (String.compare (fst c) name) == 0 then true else false) ddn))
	with | _ -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Region Field Layout not found in Data Decls";}
	
let rec get_data_decl_names (ddf : I.data_decl list) : (ident * ((I.typed_ident * loc * bool) list)) list = 
	match ddf with
	| x::xs -> (x.I.data_name, List.map (fun (a1,a2,a3,a4) -> (a1,a2,a3)) x.I.data_fields)::(get_data_decl_names xs)
	| [] -> []

let check_mem_formula_data_names (ddf : I.data_decl list) (fl : (ident * (IP.ann list))) : bool = 
	let data_name_fields = get_data_decl_names ddf in
	let name = fst fl in
	if List.mem name (fst (List.split data_name_fields))
	then if List.length (snd fl) == List.length (get_data_fields data_name_fields name) 
		then true
		else Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Number of Fields in Memory Region for "^name^" don't match with Data Decls";}
	else false
		
let check_mem_formula (vdf : I.view_decl) (ddcl : I.data_decl list) =
	match vdf.I.view_mem with
	| Some a -> (match a.IF.mem_formula_exp with
		        | IP.Var (_,_)
  			| IP.BagDiff (_,_,_) 
 			| IP.Bag(_,_)
			| IP.BagIntersect (_,_)
  			| IP.BagUnion (_,_) ->
  			let allfvs = IP.afv a.IF.mem_formula_exp in
  			let allguardvs = List.concat (List.map IP.fv a.IF.mem_formula_guards) in
            (* let all_field_value_exps = 
              List.concat (List.map (fun c -> List.concat (List.map IP.afv (snd c))) a.IF.mem_formula_field_values) in*)
  			let allvs = allfvs@allguardvs in
  			let fvs = (List.filter (fun c -> match c with 
  					| (a,Primed) 
  					| (a,Unprimed) -> if (List.mem a ("self"::vdf.I.view_vars)) then false else true) allvs) in
  			if (List.length fvs) == 0
			then 
			if List.for_all (fun v -> check_mem_formula_data_names ddcl v)  a.IF.mem_formula_field_layout
			then ()
			else Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Field Layout of "^ vdf.I.view_name ^" is not present in Data Decls";}
			else Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = 
			"[mem.ml] : Memory Spec of "^ vdf.I.view_name ^" contains free variables " ^ (Iprinter.string_of_var_list fvs);}
			| _ -> Err.report_error {
				Err.error_loc = no_pos;
				Err.error_text = "[mem.ml] : Memory Spec of "^ vdf.I.view_name ^" contains unrecognized expressions";})
	| None -> ()

let add_mem_invariant (inv : IP.formula) (vmem : IF.mem_formula option) : IP.formula =
	match vmem with
	| Some a -> let new_var = ("Anon"^(fresh_trailer()),Unprimed) in 
		let tmp_formula = IP.BForm((IP.BagNotIn(new_var, a.IF.mem_formula_exp,no_pos),None),None) in
		let tmp_formula2 = IP.mkNeqExp (IP.Var(new_var, no_pos)) (IP.Null(no_pos)) no_pos in
		let add_formula = IP.mkOr tmp_formula tmp_formula2 None no_pos in
		let mem_inv = IP.mkForall [new_var] add_formula None no_pos
		in IP.mkAnd inv mem_inv (IP.pos_of_formula inv)
	| None -> inv

let rec conv_h_formula_conj_to_star (h : CF.h_formula) : CF.h_formula = 
match h with
| CF.Conj ({ CF.h_formula_conj_h1 = f1;
	     CF.h_formula_conj_h2 = f2;
	     CF.h_formula_conj_pos = pos;}) -> 
	     CF.Star{CF.h_formula_star_h1 = (conv_h_formula_conj_to_star f1);
	     	     CF.h_formula_star_h2 = (conv_h_formula_conj_to_star f2);
	     	     CF.h_formula_star_pos = pos}
| CF.Phase ({ CF.h_formula_phase_rd = f1;
	      CF.h_formula_phase_rw = f2;
	      CF.h_formula_phase_pos = pos;})-> 
	     CF.Star{CF.h_formula_star_h1 = (conv_h_formula_conj_to_star f1);
	     	     CF.h_formula_star_h2 = (conv_h_formula_conj_to_star f2);
	     	     CF.h_formula_star_pos = pos}
	      (* Treat Phase as Conj for now*)
| _ -> h

let rec conv_formula_conj_to_star (f : CF.formula) : CF.formula = 
match f with
| CF.Or ({CF.formula_or_f1 = f1;
	  CF.formula_or_f2 = f2;
	  CF.formula_or_pos = pos})-> CF.mkOr (conv_formula_conj_to_star f1) (conv_formula_conj_to_star f2) pos
| CF.Base ({CF.formula_base_heap = h;
            CF.formula_base_pure = p;
            CF.formula_base_vperm = vp;
            CF.formula_base_type = t; 
            CF.formula_base_and = ol; 
            CF.formula_base_flow = fl;
            CF.formula_base_label = lbl;
            CF.formula_base_pos = pos}) -> CF.mkBase_w_lbl (conv_h_formula_conj_to_star h) p vp t fl ol pos lbl
| CF.Exists ({CF.formula_exists_qvars = qvars;
	      CF.formula_exists_heap = h;
              CF.formula_exists_pure = p;
              CF.formula_exists_vperm = vp;
              CF.formula_exists_type = t; 
              CF.formula_exists_and = ol; 
              CF.formula_exists_flow = fl;
              CF.formula_exists_label = lbl;
              CF.formula_exists_pos = pos}) -> CF.mkExists_w_lbl qvars (conv_h_formula_conj_to_star h) p vp t fl ol pos lbl

let rec contains_conj (f:CF.h_formula) : bool = 
(*let () = print_string ("Checking Conj = "^ (string_of_h_formula f) ^ "\n") in *)
match f with
| CF.DataNode (h1) -> false
| CF.ViewNode (h1) -> false
| CF.Star ({CF.h_formula_star_h1 = h1;
		   CF.h_formula_star_h2 = h2;
		   CF.h_formula_star_pos = pos}) 
| CF.Phase ({CF.h_formula_phase_rd = h1;
		    CF.h_formula_phase_rw = h2;
		    CF.h_formula_phase_pos = pos})-> (contains_conj h1) || (contains_conj h2)
| CF.Conj _		    
| CF.ConjStar _		    
| CF.ConjConj _ -> true
| _ -> false

let rec contains_starminus (f:CF.h_formula) : bool = 
(*let () = print_string ("Checking StarMinus = "^ (string_of_h_formula f) ^ "\n") in *)
match f with
| CF.DataNode (h1) -> false
| CF.ViewNode (h1) -> false
| CF.Star ({CF.h_formula_star_h1 = h1;
		   CF.h_formula_star_h2 = h2;
		   CF.h_formula_star_pos = pos}) 
| CF.Phase ({CF.h_formula_phase_rd = h1;
		    CF.h_formula_phase_rw = h2;
		    CF.h_formula_phase_pos = pos})
| CF.Conj({CF.h_formula_conj_h1 = h1;
		   CF.h_formula_conj_h2 = h2;
		   CF.h_formula_conj_pos = pos})
| CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
		   CF.h_formula_conjstar_h2 = h2;
		   CF.h_formula_conjstar_pos = pos})
| CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
		   CF.h_formula_conjconj_h2 = h2;
		   CF.h_formula_conjconj_pos = pos})-> (contains_starminus h1) || (contains_starminus h2)
| CF.StarMinus _ -> true
| _ -> false
              
let rec split_heap (h:CF.h_formula) : (CF.h_formula * CF.h_formula) = 
	(*let () = print_string ("Splitting Heap H = "^ (string_of_h_formula h) ^ "\n") in*)
    let () = Globals.noninter_entailments := !Globals.noninter_entailments + 1 in
	match h with
	| CF.Conj({CF.h_formula_conj_h1 = h1;
		   CF.h_formula_conj_h2 = h2;
		   CF.h_formula_conj_pos = pos})
	| CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
		   CF.h_formula_conjstar_h2 = h2;
		   CF.h_formula_conjstar_pos = pos})
	| CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
		   CF.h_formula_conjconj_h2 = h2;
		   CF.h_formula_conjconj_pos = pos})		   		   
  	| CF.Phase({CF.h_formula_phase_rd = h1;
		    CF.h_formula_phase_rw = h2;
		    CF.h_formula_phase_pos = pos}) -> 
		    (*let () = print_string ("H1 = "^ (string_of_h_formula h1)^ "\nH2 = "^ (string_of_h_formula h2) ^ "\n")
		    in*) (h1,h2)
	| CF.Star({CF.h_formula_star_h1 = h1;
		   CF.h_formula_star_h2 = h2;
		   CF.h_formula_star_pos = pos}) ->
		   if contains_conj h1 then
 		   (*let () = print_string ("H1 = "^ (string_of_h_formula h1)^ "\nH2 = "^ (string_of_h_formula h2) ^ "\n") in*)
		   let left_h_split = split_heap h1
		   in (fst left_h_split),(CF.mkStarH (snd left_h_split) h2 pos)
		   else if contains_conj h2 then
		   let right_h_split = split_heap h2
		   in (CF.mkStarH (fst right_h_split) h1 pos), (snd right_h_split)
		   else (h,CF.HEmp)
	| _ -> (h, CF.HEmp)

let split_heap (h:CF.h_formula) : (CF.h_formula * CF.h_formula) = 
  let pr = string_of_h_formula in
  let pr2 = (pr_pair string_of_h_formula string_of_h_formula) in
  Debug.no_1 "split_heap" pr pr2 split_heap h 

let rec drop_node_h_formula (h:CF.h_formula) (sv:CP.spec_var) : (CF.h_formula) = 
match h with
	| CF.DataNode _ 
	| CF.ViewNode _ -> if CP.eq_spec_var (CF.get_node_var h) sv then CF.HEmp else h
	| CF.Conj({CF.h_formula_conj_h1 = h1;
		   CF.h_formula_conj_h2 = h2;
		   CF.h_formula_conj_pos = pos}) ->
		   CF.mkConjH (drop_node_h_formula h1 sv) (drop_node_h_formula h2 sv) pos
	| CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
		   CF.h_formula_conjstar_h2 = h2;
		   CF.h_formula_conjstar_pos = pos})->
		   CF.mkConjStarH (drop_node_h_formula h1 sv) (drop_node_h_formula h2 sv) pos
	| CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
		   CF.h_formula_conjconj_h2 = h2;
		   CF.h_formula_conjconj_pos = pos}) ->
		   CF.mkConjConjH (drop_node_h_formula h1 sv) (drop_node_h_formula h2 sv) pos		   		   
  	| CF.Phase({CF.h_formula_phase_rd = h1;
		    CF.h_formula_phase_rw = h2;
		    CF.h_formula_phase_pos = pos}) -> 
		    CF.mkPhaseH (drop_node_h_formula h1 sv) (drop_node_h_formula h2 sv) pos
	| CF.Star({CF.h_formula_star_h1 = h1;
		   CF.h_formula_star_h2 = h2;
		   CF.h_formula_star_pos = pos}) ->
 		   CF.mkStarH (drop_node_h_formula h1 sv) (drop_node_h_formula h2 sv) pos
	| _ -> h

let rec find_node_starminus (h:CF.h_formula) (sv:CP.spec_var) : CF.h_formula option = 
match h with
	| CF.Conj({CF.h_formula_conj_h1 = h1;
		   CF.h_formula_conj_h2 = h2;
		   CF.h_formula_conj_pos = pos}) 
	| CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
		   CF.h_formula_conjstar_h2 = h2;
		   CF.h_formula_conjstar_pos = pos})
	| CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
		   CF.h_formula_conjconj_h2 = h2;
		   CF.h_formula_conjconj_pos = pos})	   		   
  	| CF.Phase({CF.h_formula_phase_rd = h1;
		    CF.h_formula_phase_rw = h2;
		    CF.h_formula_phase_pos = pos})
	| CF.Star({CF.h_formula_star_h1 = h1;
		   CF.h_formula_star_h2 = h2;
		   CF.h_formula_star_pos = pos}) ->
		   let sv1 = find_node_starminus h1 sv in
		   let sv2 = find_node_starminus h2 sv in
		   (match sv1,sv2 with
		   | Some(_), Some(_) -> sv1 (*shouldn't happen*)
		   | Some(_),None  -> sv1
		   | None, Some(_) -> sv2
		   | None,None -> None)
	| CF.StarMinus ({CF.h_formula_starminus_h1 = h1;
		   CF.h_formula_starminus_h2 = h2;
		   CF.h_formula_starminus_pos = pos}) ->
		   if CP.eq_spec_var (CF.get_node_var h1) sv then Some(h2) else None
	| _ -> None

let rec remove_phases (h: IF.h_formula): IF.h_formula = 
	(*let () = print_string ("Removing Phase from H = "^ (Iprinter.string_of_h_formula h) ^ "\n") in *)
	match h with
  	| IF.Phase({IF.h_formula_phase_rd = h1;
		    IF.h_formula_phase_rw = h2;
		    IF.h_formula_phase_pos = pos}) -> let h1_rp = (remove_phases h1) in
		    				let h2_rp = (remove_phases h2) in 
		    				if h1_rp = IF.HEmp then h2_rp else
		    				if h2_rp = IF.HEmp then h1_rp else
		    				IF.mkConj h1_rp h2_rp pos
	| IF.Conj({IF.h_formula_conj_h1 = h1;
		   IF.h_formula_conj_h2 = h2;
		   IF.h_formula_conj_pos = pos}) -> IF.mkConj (remove_phases h1) (remove_phases h2) pos
	| IF.Star({IF.h_formula_star_h1 = h1;
		   IF.h_formula_star_h2 = h2;
		   IF.h_formula_star_pos = pos}) -> IF.mkStar (remove_phases h1) (remove_phases h2) pos
	| _ -> h
		   
let normalize_h_formula (h : IF.h_formula): IF.h_formula =
	(*let () = print_string ("Before Phase Removal H = "^ (Iprinter.string_of_h_formula h) ^ "\n") in*)
	let res = remove_phases h in	
	(*let () = print_string ("After Phase Removal H = "^ (Iprinter.string_of_h_formula res) ^ "\n") in*) res 
	(* Push star inside A * (B /\ C) == (A * B) /\ (A * C) *) 
	(*let helper h = match h with 
	| IF.Conj({IF.h_formula_conj_h1 = h1;
		   IF.h_formula_conj_h2 = h2;
		   IF.h_formula_conj_pos = pos}) ->
	| IF.Star{IF.h_formula_star_h1 = h1;
		   IF.h_formula_star_h2 = h2;
		   IF.h_formula_star_pos = pos}) ->
	| _ -> h*)
	
let rec is_compatible_field_layout (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list): bool =	
  (* Debug.info_hprint(add_str "is_compatible_field_layout" pr_none) () Globals.no_pos ; *)
match (ann_lst_l, ann_lst_r) with
    | ([], []) -> true
    | (ann_l :: tl, ann_r :: tr ) ->
      begin
	match ann_l, ann_r with 
	  | CP.ConstAnn(Mutable), CP.ConstAnn(Accs)
  	  | CP.ConstAnn(Imm), CP.ConstAnn(Accs) 
  	  | CP.ConstAnn(Lend), CP.ConstAnn(Accs)
	  | CP.ConstAnn(Lend), CP.ConstAnn(Lend) -> true && (is_compatible_field_layout tl tr)	
  	  | CP.ConstAnn(Accs), CP.ConstAnn(Mutable)
  	  | CP.ConstAnn(Accs), CP.ConstAnn(Imm)
	  | CP.ConstAnn(Accs), CP.ConstAnn(Lend) 
  	  | CP.ConstAnn(Accs), CP.ConstAnn(Accs)-> true && (is_compatible_field_layout tl tr)
  	  | _ , _ -> false

      end
    | (_, _) ->	false
    
let rec is_same_field_layout (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list): bool =	
match (ann_lst_l, ann_lst_r) with
    | ([], []) -> true
    | (ann_l :: tl, ann_r :: tr ) ->
      begin
	match ann_l, ann_r with 
	  | CP.ConstAnn(Mutable), CP.ConstAnn(Mutable)
  	  | CP.ConstAnn(Imm), CP.ConstAnn(Imm) 
  	  | CP.ConstAnn(Lend), CP.ConstAnn(Lend)
  	  | CP.ConstAnn(Accs), CP.ConstAnn(Accs)-> true && (is_same_field_layout tl tr)
  	  | _ , _ -> false

      end
    | (_, _) ->	 false    

let rec is_compatible_field_values (ann_lst_l: CP.exp list) (ann_lst_r: CP.exp list): bool =	
match (ann_lst_l, ann_lst_r) with
    | ([], []) -> true
    | (ann_l :: tl, ann_r :: tr ) ->
      begin
	match ann_l, ann_r with 
	  | CP.Var(sv1,_),CP.Var(sv2,_) -> if CP.is_anon_var sv1 || CP.is_anon_var sv2 
        then true && (is_compatible_field_values tl tr)
        else false
      | CP.Var(sv,_),_  
      | _, CP.Var(sv,_) -> if CP.is_anon_var sv then true && (is_compatible_field_values tl tr)
        else false
  	  | _ , _ -> false
      end
    | (_, _) ->	 false   

let rec is_same_field_values (ann_lst_l: CP.exp list) (ann_lst_r: CP.exp list) (p:CP.formula) : bool =	
match (ann_lst_l, ann_lst_r) with
    | ([], []) -> true
    | (ann_l :: tl, ann_r :: tr ) ->
      begin
	match ann_l, ann_r with 
	  | CP.Var(sv1,_),CP.Var(sv2,_) -> if CP.is_anon_var sv1 || CP.is_anon_var sv2 || CP.eq_spec_var sv1 sv2 
        then true &&  (is_same_field_values tl tr p) else false 
      | CP.IConst(i1,_),CP.IConst(i2,_) -> i1==i2 && (is_same_field_values tl tr p)
      | CP.Var(sv,_), CP.IConst(i,_)
      | CP.IConst(i,_),CP.Var(sv,_) -> let checkeq = CP.mkEqExp ann_l ann_r no_pos in 
                                       (*let () = print_string("pure formula:"^(string_of_pure_formula p)) in
                                       let () = print_string("check formula:"^(string_of_pure_formula checkeq)) in*)
                                       let r,_,_ = x_add TP.imply_one 100 p checkeq "field_value_imply" false None in
                                       if r then true && (is_same_field_values tl tr p) else false
      | CP.Var(sv,_),_  
      | _, CP.Var(sv,_) -> if CP.is_anon_var sv then true && (is_same_field_values tl tr p)
        else false
  	  | _ , _ -> false
      end
    | (_, _) ->	 false    

let rec check_mem_non_inter (h1: CF.h_formula) (h2:CF.h_formula) (vl:C.view_decl list) : bool = 
	let mpf1 = fst (xmem_heap h1 vl) in
	let mpf2 = fst (xmem_heap h2 vl) in
	let mpe1,exact1,fl1 = mpf1.CF.mem_formula_exp , mpf1.CF.mem_formula_exact, mpf1.CF.mem_formula_field_layout in
	let mpe2,exact2,fl2 = mpf2.CF.mem_formula_exp , mpf2.CF.mem_formula_exact, mpf2.CF.mem_formula_field_layout in
	let t = List.map (fun f1 -> 
		let matched_fields = (List.filter (fun f2-> if (String.compare (fst f1) (fst f2)) == 0 then true else false) fl2)
		in List.exists (fun c -> (is_compatible_field_layout (snd f1) (snd c))) matched_fields) fl1
	in List.for_all (fun c -> c) t

let rec check_mem_conj (h1: CF.h_formula) (h2:CF.h_formula) (vl:C.view_decl list) : bool = 
	(*let mpf1 = fst (xmem_heap h1 vl) in
	let mpf2 = fst (xmem_heap h2 vl) in
	let mpe1,exact1,fl1 = mpf1.CF.mem_formula_exp , mpf1.CF.mem_formula_exact, mpf1.CF.mem_formula_field_layout in
	let mpe2,exact2,fl2 = mpf2.CF.mem_formula_exp , mpf2.CF.mem_formula_exact, mpf2.CF.mem_formula_field_layout in*)
	true
	
let rec check_mem_conjstar (h1: CF.h_formula) (h2:CF.h_formula) (vl:C.view_decl list) : bool = 
	let mpf1 = fst (xmem_heap h1 vl) in
	let mpf2 = fst (xmem_heap h2 vl) in
	let mpe1,exact1,fl1 = mpf1.CF.mem_formula_exp , mpf1.CF.mem_formula_exact, mpf1.CF.mem_formula_field_layout in
	let mpe2,exact2,fl2 = mpf2.CF.mem_formula_exp , mpf2.CF.mem_formula_exact, mpf2.CF.mem_formula_field_layout in
	if exact1 && exact2 then
	let t = List.map (fun f1 -> 
		let matched_fields = (List.filter (fun f2-> if (String.compare (fst f1) (fst f2)) == 0 then true else false) fl2)
		in List.exists (fun c -> (is_compatible_field_layout (snd f1) (snd c))) matched_fields) fl1
	in List.for_all (fun c -> c) t
	else false
	
let rec check_mem_conjconj (h1: CF.h_formula) (h2:CF.h_formula) (vl:C.view_decl list) : bool = 
	let mpf1 = fst (xmem_heap h1 vl) in
	let mpf2 = fst (xmem_heap h2 vl) in
	let mpe1,exact1,fl1 = mpf1.CF.mem_formula_exp , mpf1.CF.mem_formula_exact, mpf1.CF.mem_formula_field_layout in
	let mpe2,exact2,fl2 = mpf2.CF.mem_formula_exp , mpf2.CF.mem_formula_exact, mpf2.CF.mem_formula_field_layout in
	if exact1 && exact2 then 
	let t = List.map (fun f1 -> 
		let matched_fields = (List.filter (fun f2-> if (String.compare (fst f1) (fst f2)) == 0 then true else false) fl2)
		in List.exists (fun c -> (is_same_field_layout (snd f1) (snd c))) matched_fields) fl1
	in List.for_all (fun c -> c) t
	else false		

let check_mem_starminus (h1: CF.h_formula) (h2:CF.h_formula) (vl:C.view_decl list) : bool = 
	if (CF.is_data h1) || (CF.is_view h1) then if (CF.is_data h2) || (CF.is_view h2) then true
	else false else false

let rec check_mem_sat (h: CF.h_formula) (vl:C.view_decl list) : bool = 
match h with 
| CF.Conj({CF.h_formula_conj_h1 = h1;
	   CF.h_formula_conj_h2 = h2;
	   CF.h_formula_conj_pos = pos}) -> (check_mem_conj h1 h2 vl)
| CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
	   CF.h_formula_conjstar_h2 = h2;
	   CF.h_formula_conjstar_pos = pos}) -> (check_mem_conjstar h1 h2 vl)
| CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
	   CF.h_formula_conjconj_h2 = h2;
	   CF.h_formula_conjconj_pos = pos}) -> (check_mem_conjconj h1 h2 vl)	   	   
| CF.Phase({CF.h_formula_phase_rd = h1;
	    CF.h_formula_phase_rw = h2;
	    CF.h_formula_phase_pos = pos})
| CF.Star({CF.h_formula_star_h1 = h1;
	   CF.h_formula_star_h2 = h2;
	   CF.h_formula_star_pos = pos}) -> (check_mem_sat h1 vl) && (check_mem_sat h2 vl)
| CF.StarMinus({CF.h_formula_starminus_h1 = h1;
	   CF.h_formula_starminus_h2 = h2;
	   CF.h_formula_starminus_pos = pos}) -> (check_mem_starminus h1 h2 vl)
| _ -> true

let check_mem_sat (h: CF.h_formula) (vl:C.view_decl list) : bool = 
Debug.no_1 "check_mem_sat" string_of_h_formula string_of_bool (fun c -> check_mem_sat c vl) h 

let rec make_list_of_h_formula (h: CF.h_formula) : CF.h_formula list =
match h with 
| CF.Conj({CF.h_formula_conj_h1 = h1;
	   CF.h_formula_conj_h2 = h2;
	   CF.h_formula_conj_pos = pos}) 
| CF.Phase({CF.h_formula_phase_rd = h1;
	    CF.h_formula_phase_rw = h2;
	    CF.h_formula_phase_pos = pos})
| CF.Star({CF.h_formula_star_h1 = h1;
	   CF.h_formula_star_h2 = h2;
	   CF.h_formula_star_pos = pos}) -> (make_list_of_h_formula h1)@(make_list_of_h_formula h2)
| _ -> [h]

(*let rec matched_mem_heap (h1:CF.h_formula) (h2:CF.h_formula) (vl:C.view_decl list): (CF.h_formula * CF.h_formula) = 
	(*let list_of_data_nodes = List.filter (CF.is_data) make_list_of_h_formula h2 in*)
	let mpf1 = fst (xmem_heap h1 vl) in
	let mpe1,exact1,fl1 = mpf1.CF.mem_formula_exp, mpf1.CF.mem_formula_exact, mpf1.CF.mem_formula_field_layout in
	match h2 with
	| CF.Conj({CF.h_formula_conj_h1 = h1;
		   CF.h_formula_conj_h2 = h2;
		   CF.h_formula_conj_pos = pos}) 
	| CF.Phase({CF.h_formula_phase_rd = h1;
		    CF.h_formula_phase_rw = h2;
		    CF.h_formula_phase_pos = pos})
	| CF.Star({CF.h_formula_star_h1 = h1;
		   CF.h_formula_star_h2 = h2;
		   CF.h_formula_star_pos = pos}) -> (make_list_of_h_formula h1)@(make_list_of_h_formula h2)
	| _ -> [h]

	let matched_data_nodes = match_mem_formula_data fl1 list_of_data_nodes in
 *) 
 
let rec transform_to_tmp_ann (ann_lst: CP.ann list) : CP.ann list =
  match ann_lst with
    | [] -> []
    | ann_l::tl ->
      begin
	match ann_l with 
	  | CP.ConstAnn(ann)  -> CP.TempAnn(CP.ConstAnn(ann)) :: (transform_to_tmp_ann tl)
	  | _ -> ann_l :: (transform_to_tmp_ann tl)
      end

let rec join_ann (ann1: CP.ann list) (ann2: CP.ann list) (param1: CP.spec_var list) (param2: CP.spec_var list):
 bool * (CP.ann list) * (CP.spec_var list) (* * CP.formula*) =
 (*let tf = CP.mkTrue no_pos in*)
  match ann1, ann2,param1,param2 with
    | [], [],[],[] -> (true,[],[](*,tf*))
    | (CP.ConstAnn(Accs))::t1, a::t2, [], []
    | a::t1, (CP.ConstAnn(Accs))::t2, [], [] -> let compatible, new_ann, _(*, new_p*) = join_ann t1 t2 [] []  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, a::new_ann, [](*, (CP.mkAnd p new_p no_pos)*))
    | (CP.ConstAnn(Accs))::t1, a::t2, p::pt1, pa::pt2 
    | a::t1, (CP.ConstAnn(Accs))::t2, pa::pt1, p::pt2 -> let compatible, new_ann, new_param(*, new_p*) = join_ann t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, a::new_ann, pa::new_param(*, (CP.mkAnd p new_p no_pos)*))
    (* | (CP.TempRes(a1,a2))::t1, a::t2, p::pt1, pa::pt2  *)
    (* | a::t1, (CP.TempRes(a1,a2))::t2, pa::pt1, p::pt2 -> *)
    (*       let compatible, new_ann, new_param(\*, new_p*\) = join_ann t1 t2 pt1 pt2  in *)
    (* 	  (\*let p = CP.mkEqVar *\) *)
    (*       let compatible = compatible  *)
    (*       (compatible, a::new_ann, pa::new_param(\*, (CP.mkAnd p new_p no_pos)*\)) *)
    | _ -> (false,[],[](*,tf*))
    
let rec join_ann_conj (ann1: CP.ann list) (ann2: CP.ann list) (param1: CP.spec_var list) (param2: CP.spec_var list):
 bool * (CP.ann list) * (CP.spec_var list) (* * CP.formula*) =
 (*let tf = CP.mkTrue no_pos in*)
  match ann1, ann2,param1,param2 with
    | [], [],[],[] -> (true,[],[](*,tf*))
    | (CP.ConstAnn(Accs))::t1, a::t2, p::pt1, pa::pt2 
    | a::t1, (CP.ConstAnn(Accs))::t2, pa::pt1, p::pt2 -> let compatible, new_ann, new_param(*, new_p*) = join_ann_conj t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, a::new_ann, pa::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | a1::t1, a2::t2, p::pt1, pa::pt2 -> let compatible, new_ann, new_param(*, new_p*) = join_ann_conj t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, a1::new_ann, p::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | _ -> (false,[],[](*,tf*))
    
let rec join_ann_conjstar (ann1: CP.ann list) (ann2: CP.ann list) (param1: CP.spec_var list) (param2: CP.spec_var list):
 bool * (CP.ann list) * (CP.spec_var list) (* * CP.formula*) =
 (*let tf = CP.mkTrue no_pos in*)
  match ann1, ann2,param1,param2 with
    | [], [],[],[] -> (true,[],[](*,tf*))
    | (CP.ConstAnn(Accs))::t1, a::t2, p::pt1, pa::pt2 
    | a::t1, (CP.ConstAnn(Accs))::t2, pa::pt1, p::pt2 -> 
    				let compatible, new_ann, new_param(*, new_p*) = join_ann_conjstar t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, a::new_ann, pa::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | (CP.ConstAnn(Lend))::t1, (CP.ConstAnn(Lend))::t2, p1::pt1, p2::pt2  -> 
    				let compatible, new_ann, new_param(*, new_p*) = join_ann_conjstar t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, (CP.ConstAnn(Lend))::new_ann, p1::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | _ -> (false,[],[](*,tf*))
    

let rec join_ann_conjconj (ann1: CP.ann list) (ann2: CP.ann list) (param1: CP.spec_var list) (param2: CP.spec_var list):
 bool * (CP.ann list) * (CP.spec_var list) (* * CP.formula*) =
 (*let tf = CP.mkTrue no_pos in*)
  match ann1, ann2,param1,param2 with
    | [], [],[],[] -> (true,[],[](*,tf*))
    | CP.ConstAnn(ha1)::t1, CP.ConstAnn(ha2)::t2, p1::pt1, p2::pt2 -> 
    			let compatible, new_ann, new_param(*, new_p*) = join_ann_conjconj t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (ha1==ha2 && compatible, CP.ConstAnn(ha1)::new_ann, p1::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | _ -> (false,[],[](*,tf*))        

let compact_data_nodes (h1: CF.h_formula) (h2: CF.h_formula) (aset:CP.spec_var list list) func
: CF.h_formula * CF.h_formula * CP.formula =
(match h1 with
| CF.DataNode 
	{CF.h_formula_data_name = name1;
         CF.h_formula_data_node = v1;
         CF.h_formula_data_param_imm = param_ann1;
         CF.h_formula_data_arguments = h1args;
         } ->
	 let aset_sv = Csvutil.get_aset aset v1 in
         (match h2 with
 	 | CF.DataNode { CF.h_formula_data_name = name2;
 	                 CF.h_formula_data_node = v2;
 	                 CF.h_formula_data_param_imm = param_ann2; 
 	                 CF.h_formula_data_arguments = h2args;} ->
         (* h1, h2 nodes; check if they can be join into a single node. If so, h1 will contain the updated annotations, while 
            h2 will be replaced by "emp". Otherwise both data nodes will remain unchanged *)
 		     if (String.compare name1 name2 == 0) && ((CP.mem v2 aset_sv) || (CP.eq_spec_var v1 v2)) then
 		         let compatible, new_param_imm, new_args = func param_ann1 param_ann2 h1args h2args  in
	                (* compact to keep the updated node*)
                 if(not(CP.is_primed v2) || (CP.is_primed v1)) then
	                 (match h1 with (* this match is to avoid the rewriting of all h1 parameters*)
	                  | CF.DataNode h -> 
	                  	  if (compatible == true) then 
	                  let comb_list = 
	                  (List.combine h.CF.h_formula_data_arguments h2args) in
	                   let p = CP.conj_of_list 
		          (List.map (fun c -> (CP.mkEqVar (fst c) (snd c) h.CF.h_formula_data_pos)) comb_list) 				   h.CF.h_formula_data_pos
			   in 
			   	(CF.DataNode {h with CF.h_formula_data_arguments = new_args; 			
			     	 CF.h_formula_data_param_imm = new_param_imm}, CF.HEmp, p)
			  	          else (CF.HFalse, h2, (CP.mkTrue no_pos))
 			  | _ -> (h1, h2,(CP.mkTrue no_pos)) (* will never reach this branch *))
	             else (*keep v2*)
 			  (match h2 with (* this match is to avoid the rewriting of all h2 parameters*)
 			   | CF.DataNode h -> 
			         if (compatible == true) then 
			         let comb_list = 
			         (List.combine h.CF.h_formula_data_arguments h1args) in
			          let p = CP.conj_of_list 
			        (List.map (fun c -> (CP.mkEqVar (fst c) (snd c) h.CF.h_formula_data_pos)) comb_list) 				          h.CF.h_formula_data_pos
			         in
			         (CF.DataNode {h with CF.h_formula_data_arguments = new_args;
			          CF.h_formula_data_param_imm = new_param_imm},CF.HEmp,p)
			          else (CF.HFalse,h1,(CP.mkTrue no_pos))
 			   | _ -> (h1, h2,(CP.mkTrue no_pos)) (* will never reach this branch *))
		     else (h1, h2,(CP.mkTrue no_pos)) (* h2 is not an alias of h1 *) 
	| _ -> (h1,h2,(CP.mkTrue no_pos))  (*shouldn't get here*))
| _ -> (h1,h2,(CP.mkTrue no_pos)) (*shouldn't get here*))

let compact_data_nodes (h1: CF.h_formula) (h2: CF.h_formula) (aset:CP.spec_var list list) func
: CF.h_formula * CF.h_formula * CP.formula =
  let pr = string_of_h_formula in
  let pr2 = string_of_pure_formula in
  Debug.no_3 "compact_data_nodes" pr pr (pr_list (pr_list string_of_spec_var)) (pr_triple pr pr pr2) (fun _ _ _ -> compact_data_nodes h1 h2 aset func) h1 h2 aset

let compact_view_nodes (h1: CF.h_formula) (h2: CF.h_formula) (aset:CP.spec_var list list) func
      : CF.h_formula * CF.h_formula * CP.formula =
  (match h1 with
    | CF.ViewNode 
	    {CF.h_formula_view_name = name1;
            CF.h_formula_view_node = v1;
            CF.h_formula_view_annot_arg = annot_arg1;
            } ->
          let param_ann1 = CP.annot_arg_to_imm_ann_list (List.map fst annot_arg1) in
          let aset_sv = Csvutil.get_aset aset v1 in
          (match h2 with
 	    | CF.ViewNode { CF.h_formula_view_name = name2;
 	      CF.h_formula_view_node = v2;
 	      CF.h_formula_view_annot_arg = annot_arg2;} ->
                  let param_ann2 = CP.annot_arg_to_imm_ann_list (List.map fst annot_arg2 ) in
                  (* h1, h2 nodes; check if they can be join into a single node. If so, h1 will contain the updated annotations, while 
                     h2 will be replaced by "emp". Otherwise both data nodes will remain unchanged *)
 		  if (String.compare name1 name2 == 0) && ((CP.mem v2 aset_sv) || (CP.eq_spec_var v1 v2)) then
 		    let compatible, new_param_imm, _ = func param_ann1 param_ann2 [] []  in
	            (* compact to keep the updated node*)
		    if (compatible == true) then 
                      (match h1 with 
                        | CF.ViewNode h ->
			      (CF.ViewNode {h with 
                                  CF.h_formula_view_annot_arg = CP.update_positions_for_imm_view_params new_param_imm h.CF.h_formula_view_annot_arg;},
                              CF.HEmp, (CP.mkTrue no_pos))
                        | _ -> (h1, h2,(CP.mkTrue no_pos))
                      )
		    else
                      (* to detect if contradiction exists thru heap map *)
                      (* let () = Debug.info_pprint "false here" no_pos in *)
                      (* (CF.HFalse, h2, (CP.mkTrue no_pos)) *)
                      (h1, h2, (CP.mkTrue no_pos))
                 else (h1, h2,(CP.mkTrue no_pos)) (* h2 is not an alias of h1 *) 
	    | _ -> (h1,h2,(CP.mkTrue no_pos))  (*shouldn't get here*))
    | _ -> (h1,h2,(CP.mkTrue no_pos)) (*shouldn't get here*))

let compact_view_nodes (h1: CF.h_formula) (h2: CF.h_formula) (aset:CP.spec_var list list) func
: CF.h_formula * CF.h_formula * CP.formula =
  let pr = string_of_h_formula in
  let pr2 = string_of_pure_formula in
  Debug.no_3 "compact_view_nodes" pr pr (pr_list (pr_list string_of_spec_var)) (pr_triple pr pr pr2) (fun _ _ _ -> compact_view_nodes h1 h2 aset func) h1 h2 aset

let rec compact_nodes_with_same_name_in_h_formula_x (f: CF.h_formula) (aset: CP.spec_var list list) : CF.h_formula * CP.formula = 
  (*let () = print_string("Compacting :"^ (string_of_h_formula f)^ "\n") in*)
  if not (!Globals.allow_field_ann) then f,(CP.mkTrue no_pos) else
    match f with
      | CF.Star {CF.h_formula_star_h1 = h1;
                 CF.h_formula_star_h2 = h2;
                 CF.h_formula_star_pos = pos } ->             
	let h1,h2,_ = compact_nodes_op h1 h2 aset join_ann in
	let res = CF.mkStarH h1 h2 pos in
	res,(CP.mkTrue no_pos)
      | CF.Conj{CF.h_formula_conj_h1 = h1;
		CF.h_formula_conj_h2 = h2;
	        CF.h_formula_conj_pos = pos} ->
	        let h1,h2,_ = compact_nodes_op h1 h2 aset join_ann_conj in
		let res = CF.mkConjH h1 h2 pos in
		res,(CP.mkTrue no_pos)
	        (*let h1_h,h1_p = compact_nodes_with_same_name_in_h_formula h.CF.h_formula_conj_h1 aset in
      		let h2_h,h2_p = compact_nodes_with_same_name_in_h_formula h.CF.h_formula_conj_h2 aset in
      		let and_p = CP.mkAnd h1_p h2_p h.CF.h_formula_conj_pos in
      	        CF.Conj {h with CF.h_formula_conj_h1 = h1_h;
 	        CF.h_formula_conj_h2 = h2_h;},and_p*)
      | CF.ConjStar{CF.h_formula_conjstar_h1 = h1;
		CF.h_formula_conjstar_h2 = h2;
	        CF.h_formula_conjstar_pos = pos} ->
	        let h1,h2,_ = compact_nodes_op h1 h2 aset join_ann_conjstar in
		let res = CF.mkConjStarH h1 h2 pos in
		res,(CP.mkTrue no_pos)
      | CF.ConjConj{CF.h_formula_conjconj_h1 = h1;
		CF.h_formula_conjconj_h2 = h2;
	        CF.h_formula_conjconj_pos = pos} ->
	        let h1,h2,p = compact_nodes_op h1 h2 aset join_ann_conjconj in
		let res = CF.mkConjConjH h1 h2 pos in
		res,p		 	        
      | CF.StarMinus{CF.h_formula_starminus_h1 = h1;
		CF.h_formula_starminus_h2 = h2;
        CF.h_formula_starminus_aliasing = al;
	        CF.h_formula_starminus_pos = pos} ->
	        let h1,h2,p = compact_nodes_op h1 h2 aset join_ann in
		let res = CF.mkStarMinusH h1 h2 al pos 21 in
		res,p
      | CF.Phase h ->  let h1_h,h1_p = compact_nodes_with_same_name_in_h_formula h.CF.h_formula_phase_rd aset in
      		let h2_h,h2_p = compact_nodes_with_same_name_in_h_formula h.CF.h_formula_phase_rw aset in
      		let todo_unk = CP.mkAnd h1_p h2_p h.CF.h_formula_phase_pos in
      		CF.Phase {h with CF.h_formula_phase_rd = h1_h;
 	      CF.h_formula_phase_rw = h2_h;},(CP.mkTrue no_pos)
      | _ -> f,(CP.mkTrue no_pos)


and compact_nodes_with_same_name_in_h_formula (f: CF.h_formula) (aset: CP.spec_var list list) : CF.h_formula * CP.formula =
  let pr1 = Cprinter.prtt_string_of_h_formula in
  let pr2 = !CP.print_formula in
  Debug.no_2 "compact_nodes_with_same_name_in_h_formula" pr1 (pr_list !CP.print_svl) (pr_pair pr1 pr2)
      (fun _ _ -> compact_nodes_with_same_name_in_h_formula_x f aset) f aset

and compact_nodes_op (h1: CF.h_formula) (h2: CF.h_formula) (aset:CP.spec_var list list) func 
: CF.h_formula * CF.h_formula * CP.formula =  
(match h1 with
 	          | CF.DataNode { CF.h_formula_data_name = name1;
 		                      CF.h_formula_data_node = v1;
 		                      CF.h_formula_data_param_imm = param_ann1;
 		                      CF.h_formula_data_arguments = h1args;
 		                    } ->
 		        let res_h1,res_h2,res_p =             
 	                match h2 with
 	      	          | CF.DataNode { CF.h_formula_data_name = name2;
 		                              CF.h_formula_data_node = v2;
 		                              CF.h_formula_data_param_imm = param_ann2; 
 		                              CF.h_formula_data_arguments = h2args;} ->
 		                              compact_data_nodes h1 h2 aset func
		          | CF.Star {CF.h_formula_star_h1 = h21;
			                     CF.h_formula_star_h2 = h22;
			                     CF.h_formula_star_pos = pos2 } ->
(* h1 node, h2 star formula. Try to unify h1 with nodes on the left hand side of h2 star-formula, resulting in a new h1
which will be checked against the right side of h2 star-formula. This will result in updated part of h2 right and left hand side of '*'.
Rejoin h2 star fomula, and apply compact_nodes_with_same_name_in_h_formula_x on the updated h2 to check for other groups of aliases. *)
		          	  let h31, h32,p3 = compact_nodes_op h1 h21 aset func in
		                  let h41, h42,p4 = compact_nodes_op h31 h22 aset func in
		                  let new_h2 = CF.mkStarH h32 h42 pos2 in
		                  let new_p2 = CP.mkAnd p3 p4 pos2 in
                                  let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		                  h41, new_h2 , (CP.mkAnd new_p new_p2 pos2)
		          | CF.Conj {CF.h_formula_conj_h1 = h21;
					 CF.h_formula_conj_h2 = h22;
			                 CF.h_formula_conj_pos = pos2} -> 
			          let h31, h32,p3 = compact_nodes_op h1 h21 aset func in
		                  let h41, h42,p4 = compact_nodes_op h31 h22 aset func in
		                  let new_h2 = CF.mkConjH h32 h42 pos2 in
		                  let new_p2 = CP.mkAnd p3 p4 pos2 in
                                  let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		                  h41, new_h2 , (CP.mkAnd new_p new_p2 pos2)
		          | CF.ConjStar {CF.h_formula_conjstar_h1 = h21;
					 CF.h_formula_conjstar_h2 = h22;
			                 CF.h_formula_conjstar_pos = pos2} -> 
			          let h31, h32,p3 = compact_nodes_op h1 h21 aset func in
		                  let h41, h42,p4 = compact_nodes_op h31 h22 aset func in
		                  let new_h2 = CF.mkConjStarH h32 h42 pos2 in
		                  let new_p2 = CP.mkAnd p3 p4 pos2 in
                                  let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		                  h41, new_h2 , (CP.mkAnd new_p new_p2 pos2)
		          | CF.ConjConj {CF.h_formula_conjconj_h1 = h21;
					 CF.h_formula_conjconj_h2 = h22;
			                 CF.h_formula_conjconj_pos = pos2} -> 
			          let h31, h32,p3 = compact_nodes_op h1 h21 aset func in
		                  let h41, h42,p4 = compact_nodes_op h31 h22 aset func in
		                  let new_h2 = CF.mkConjConjH h32 h42 pos2 in
		                  let new_p2 = CP.mkAnd p3 p4 pos2 in
                                  let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		                  h41, new_h2 , (CP.mkAnd new_p new_p2 pos2)
		          | CF.StarMinus {CF.h_formula_starminus_h1 = h21;
					 CF.h_formula_starminus_h2 = h22;
                     CF.h_formula_starminus_aliasing =al;
			                 CF.h_formula_starminus_pos = pos2} -> 
			          let h31, h32,p3 = compact_nodes_op h1 h21 aset func in
		                  let h41, h42,p4 = compact_nodes_op h31 h22 aset func in
		                  let new_h2 = CF.mkStarMinusH h32 h42 al pos2 22 in
		                  let new_p2 = CP.mkAnd p3 p4 pos2 in
                                  let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		                  h41, new_h2 , (CP.mkAnd new_p new_p2 pos2)	       	               		                  
		          | _ -> (h1, h2,(CP.mkTrue no_pos)) in
		      	res_h1, res_h2,res_p
              | CF.ViewNode {CF.h_formula_view_node = vn1;
                             CF.h_formula_view_name = name1;
                             CF.h_formula_view_pos = pos1} ->
                  (match h2 with
 	      	          | CF.ViewNode { CF.h_formula_view_node = vn2;
 		                              CF.h_formula_view_name = name2;
 		                              CF.h_formula_view_pos = pos1} ->
 		                              compact_view_nodes h1 h2 aset func
                      | _ ->  h1,h2,(CP.mkTrue no_pos)
                  )
	          | CF.Star {CF.h_formula_star_h1 = h11;
		                 CF.h_formula_star_h2 = h12;
		                 CF.h_formula_star_pos = pos1 } ->
		      let h31,h32,p3 = compact_nodes_op h11 h2 aset func in
		      let h41,h42,p4 = compact_nodes_op h12 h32 aset func in
		      let new_h2 = CF.mkStarH h31 h41 pos1 in
		      let new_p2 = CP.mkAnd p3 p4 pos1 in
                      let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		      new_h2, h42 , (CP.mkAnd new_p new_p2 pos1)
	          | CF.Conj {CF.h_formula_conj_h1 = h11;
				CF.h_formula_conj_h2 = h12;
			        CF.h_formula_conj_pos = pos1} ->
		      let h31,h32,p3 = compact_nodes_op h11 h2 aset func in
		      let h41,h42,p4 = compact_nodes_op h12 h32 aset func in
		      let new_h2 = CF.mkConjH h31 h41 pos1 in
		      let new_p2 = CP.mkAnd p3 p4 pos1 in
                      let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		      new_h2,h42 , (CP.mkAnd new_p new_p2 pos1)
	          | CF.ConjStar {CF.h_formula_conjstar_h1 = h11;
				CF.h_formula_conjstar_h2 = h12;
			        CF.h_formula_conjstar_pos = pos1} ->
		      let h31,h32,p3 = compact_nodes_op h11 h2 aset func in
		      let h41,h42,p4 = compact_nodes_op h12 h32 aset func in
		      let new_h2 = CF.mkConjStarH h31 h41 pos1 in
		      let new_p2 = CP.mkAnd p3 p4 pos1 in
                      let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		      new_h2,h42 , (CP.mkAnd new_p new_p2 pos1)
	          | CF.ConjConj {CF.h_formula_conjconj_h1 = h11;
				CF.h_formula_conjconj_h2 = h12;
			        CF.h_formula_conjconj_pos = pos1} ->
		      let h31,h32,p3 = compact_nodes_op h11 h2 aset func in
		      let h41,h42,p4 = compact_nodes_op h12 h32 aset func in
		      let new_h2 = CF.mkConjConjH h31 h41 pos1 in
		      let new_p2 = CP.mkAnd p3 p4 pos1 in
                      let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		      new_h2, h42 , (CP.mkAnd new_p new_p2 pos1)
	          | CF.StarMinus {CF.h_formula_starminus_h1 = h11;
				CF.h_formula_starminus_h2 = h12;
                CF.h_formula_starminus_aliasing = al;
			        CF.h_formula_starminus_pos = pos1} ->
		      let h31,h32,p3 = compact_nodes_op h11 h2 aset func in
		      let h41,h42,p4 = compact_nodes_op h12 h32 aset func in
		      let new_h2 = CF.mkStarMinusH h31 h41 al pos1 23 in
		      let new_p2 = CP.mkAnd p3 p4 pos1 in
                      let new_h2, new_p = compact_nodes_with_same_name_in_h_formula new_h2 aset in 
		      new_h2, h42 , (CP.mkAnd new_p new_p2 pos1)		               		     
	              (*let new_h2 = CF.mkConjConjH h12 h2 pos1 in
	              let h31, h32, p3 = compact_nodes_op h11 new_h2 aset func in
                      let new_h2,new_p2 = compact_nodes_with_same_name_in_h_formula h32 aset in 
	              h31, new_h2,(CP.mkAnd p3 new_p2 pos1)*)	              	              	              
		  | _ -> h1,h2,(CP.mkTrue no_pos))  

let compact_nodes_with_same_name_in_h_formula_top (f: CF.h_formula) (aset: CP.spec_var list list) : CF.h_formula * CP.formula = 
  let pr = pr_pair string_of_h_formula string_of_pure_formula in 
  Debug.no_1 "compact_nodes_with_same_name_in_h_formula_top" string_of_h_formula pr (fun c -> compact_nodes_with_same_name_in_h_formula c aset) f

let rec compact_nodes_with_same_name_in_formula (cf: CF.formula): CF.formula =
  match cf with
    | CF.Base f   -> let new_h,new_p = 
    	compact_nodes_with_same_name_in_h_formula_top f.CF.formula_base_heap (Csvutil.comp_aliases f.CF.formula_base_pure)
    	in 
    	let new_mcp = MCP.merge_mems f.CF.formula_base_pure (MCP.mix_of_pure new_p) true in
    	CF.Base { f with
        CF.formula_base_heap = new_h;       
	CF.formula_base_pure = new_mcp;}
    | CF.Or f     -> CF.Or { f with 
        CF.formula_or_f1 = compact_nodes_with_same_name_in_formula f.CF.formula_or_f1; 
        CF.formula_or_f2 = compact_nodes_with_same_name_in_formula f.CF.formula_or_f2; }
    | CF.Exists f -> 
    	let qevars = f.CF.formula_exists_qvars in 
    	(*let fvars = CP.fresh_spec_vars qevars in
    	let h = CF.subst_avoid_capture_h qevars fvars f.CF.formula_exists_heap in
    	let p = MCP.subst_avoid_capture_memo qevars fvars f.CF.formula_exists_pure in*)
    	let h = f.CF.formula_exists_heap in
    	let mp = f.CF.formula_exists_pure in
    	let new_h,new_p = 
    	compact_nodes_with_same_name_in_h_formula_top h (Csvutil.comp_aliases mp)
    	in
    	(*let p_list = List.filter (fun c -> match c with
    	| CP.BForm((CP.Eq (e1,e2,_),None),None) -> (match e1,e2 with
    				| CP.Var(s1,_) , CP.Var(s2,_) -> not ((List.mem s1 qevars) || (List.mem s2 qevars))
    				| _ -> false)
    	| _ -> false) (CP.list_of_conjs new_p) in
    	let new_p = CP.conj_of_list p_list f.CF.formula_exists_pos in*)
 	let new_mcp = MCP.merge_mems mp (MCP.mix_of_pure new_p) true in
	(*let new_mcp = MCP.memo_pure_push_exists f.CF.formula_exists_qvars new_mcp in*)
    	CF.Exists { f with
    	CF.formula_exists_qvars = qevars;
        CF.formula_exists_heap = new_h;
        CF.formula_exists_pure = new_mcp;}

let compact_nodes_with_same_name_in_formula (f: CF.formula) : CF.formula  =
  let pr1 = Cprinter.prtt_string_of_formula in
  Debug.no_1 "compact_nodes_with_same_name_in_formula" pr1 pr1
      (fun _ -> compact_nodes_with_same_name_in_formula f) f

let rec compact_nodes_with_same_name_in_struc (f: CF.struc_formula): CF.struc_formula = (* f *)
  if not (!Globals.allow_field_ann ) then f
  else
    match f with
      | CF.EList sf          -> CF.EList  (map_l_snd compact_nodes_with_same_name_in_struc sf) 
      | CF.ECase sf          -> CF.ECase {sf with CF.formula_case_branches = map_l_snd compact_nodes_with_same_name_in_struc sf.CF.formula_case_branches;} 
      | CF.EBase sf          -> CF.EBase {sf with
          CF.formula_struc_base =  compact_nodes_with_same_name_in_formula sf.CF.formula_struc_base;
          CF.formula_struc_continuation = map_opt compact_nodes_with_same_name_in_struc sf.CF.formula_struc_continuation; }
      | CF.EAssume b -> CF.EAssume {b with
		CF.formula_assume_simpl = compact_nodes_with_same_name_in_formula b.CF.formula_assume_simpl;
		CF.formula_assume_struc = compact_nodes_with_same_name_in_struc b.CF.formula_assume_struc;}
      | CF.EInfer sf         -> CF.EInfer {sf with CF.formula_inf_continuation = compact_nodes_with_same_name_in_struc sf.CF.formula_inf_continuation}
        
let rec is_lend_h_formula (f : CF.h_formula) : bool =  match f with
  | CF.DataNode (h1) -> 
        if (CP.isLend h1.CF.h_formula_data_imm) then
          (* let () = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n")  in *) true
        else
        if !Globals.allow_field_ann && (Imm.isExistsLendList h1.CF.h_formula_data_param_imm) then true
        else
          false
  | CF.ViewNode (h1) ->
        let anns = CP.annot_arg_to_imm_ann_list (CF.get_node_annot_args  f) in 
        let islend = List.exists CP.isLend anns in
        if (CP.isLend h1.CF.h_formula_view_imm) || (islend) then
          (* let () = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n") in *) true
        else
          false
  | CF.Conj({CF.h_formula_conj_h1 = h1;
	CF.h_formula_conj_h2 = h2;
	CF.h_formula_conj_pos = pos})
  | CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
	CF.h_formula_conjstar_h2 = h2;
	CF.h_formula_conjstar_pos = pos})	
  | CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
	CF.h_formula_conjconj_h2 = h2;
	CF.h_formula_conjconj_pos = pos})
  | CF.Phase({CF.h_formula_phase_rd = h1;
	CF.h_formula_phase_rw = h2;
	CF.h_formula_phase_pos = pos})
  | CF.Star({CF.h_formula_star_h1 = h1;
	CF.h_formula_star_h2 = h2;
	CF.h_formula_star_pos = pos}) -> (is_lend_h_formula h1) || (is_lend_h_formula h2)
  | CF.Hole _ -> false
  | _ -> false
  
        
let rec is_lend (f : CF.formula) : bool =  
(match f with
  | CF.Base(bf) -> is_lend_h_formula bf.CF.formula_base_heap
  | CF.Exists(ef) -> is_lend_h_formula ef.CF.formula_exists_heap
  | CF.Or({CF.formula_or_f1 = f1;
    CF.formula_or_f2 = f2;
    CF.formula_or_pos = pos}) ->
        (is_lend f1) || (is_lend f2))
        
let subtype_sv_ann_gen (impl_vars: CP.spec_var list) (l: CP.spec_var) (r: CP.spec_var) 
: bool * (CP.formula option) * (CP.formula option)  * (CP.formula option)=
	let l = CP.Var(l,no_pos) in
	let r = CP.Var(r,no_pos) in
	let c = CP.BForm ((CP.SubAnn(l,r,no_pos),None), None) in
        (* implicit instantiation of @v made stronger into an equality *)
        (* two examples in ann1.slk fail otherwise; unsound when we have *)
        (* multiple implicit being instantiated ; use explicit if needed *)
        let lhs = CP.BForm ((CP.Eq(l,r,no_pos),None), None) in
        (*let lhs = c in *)
        begin
          match r with
            | CP.Var(v,_) -> 
                if CP.mem v impl_vars then (true,Some lhs,None, None)
                else (true,None,(* Some c *)None, None)
            | _ -> (true,None,(* Some c *)None, None)
        end

let rec subtype_sv_ann_gen_list (impl_vars: CP.spec_var list) (ls: CP.spec_var list) (rs: CP.spec_var list)
: bool * (CP.formula option) * (CP.formula option) * (CP.formula option) = 
match ls, rs with
| [], [] -> (true,None,None,None)
| l::ls, r::rs -> let f, lhs, rhs, rhs_ex = (subtype_sv_ann_gen impl_vars l r) in
		  let fs, lhsls, rhsrs, rhsrs_ex = (subtype_sv_ann_gen_list impl_vars ls rs) in
		  (f && fs, (Imm.mkAndOpt lhs lhsls) , (Imm.mkAndOpt rhs rhsrs), (Imm.mkAndOpt rhs_ex rhsrs_ex))
| _,_ -> 
      (false,None,None, None)(* shouldn't get here *)


let rec get_may_aliases (sv:CP.spec_var) (h: CF.h_formula) : (CP.spec_var) list =
match h with 
  | CF.DataNode ({CF.h_formula_data_node = hsv}) -> [hsv]
  | CF.ViewNode ({CF.h_formula_view_node = hsv}) -> [hsv]
  | CF.Conj({CF.h_formula_conj_h1 = h1;
	CF.h_formula_conj_h2 = h2;
	CF.h_formula_conj_pos = pos})
  | CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
	CF.h_formula_conjstar_h2 = h2;
	CF.h_formula_conjstar_pos = pos})	
  | CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
	CF.h_formula_conjconj_h2 = h2;
	CF.h_formula_conjconj_pos = pos}) -> let l = get_may_aliases sv h1 in
					let r = get_may_aliases sv h2 in
					if List.mem sv l then r
					else if List.mem sv r then l
					else []
  | CF.Phase({CF.h_formula_phase_rd = h1;
	CF.h_formula_phase_rw = h2;
	CF.h_formula_phase_pos = pos})
  | CF.Star({CF.h_formula_star_h1 = h1;
	CF.h_formula_star_h2 = h2;
	CF.h_formula_star_pos = pos}) -> (get_may_aliases sv h1) @ (get_may_aliases sv h2)
  | _ -> []
  
let ramify_assign v rhs es = 
	let f = es.CF.es_formula in
	let h,p,_,fl,t,a = CF.split_components f in
	let t = Gen.unsome (C.type_of_exp rhs) in
        let var = (CP.SpecVar (t, v, Unprimed)) in
	(*let () = print_string("\nAssign : "^(string_of_formula f)^"\n") in*)
	let () = print_string("\nMay Aliases: "^(string_of_list_f string_of_spec_var (get_may_aliases var h))^"\n")
	in CF.Ctx es

let rec split_into_list f = match f with
  | CF.Phase({CF.h_formula_phase_rd = h1;
	CF.h_formula_phase_rw = h2;
	CF.h_formula_phase_pos = pos})
  | CF.Star({CF.h_formula_star_h1 = h1;
	CF.h_formula_star_h2 = h2;
	CF.h_formula_star_pos = pos}) 
  | CF.Conj({CF.h_formula_conj_h1 = h1;
	CF.h_formula_conj_h2 = h2;
	CF.h_formula_conj_pos = pos})
  | CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
	CF.h_formula_conjstar_h2 = h2;
	CF.h_formula_conjstar_pos = pos})	
  | CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
	CF.h_formula_conjconj_h2 = h2;
	CF.h_formula_conjconj_pos = pos}) -> List.append (split_into_list h1) (split_into_list h2)
  | CF.DataNode _
  | CF.ViewNode _ -> [f]	
  | _ -> []


let ramify_star_one (h1: CF.h_formula) (h1mpf: CF.mem_perm_formula option) (h2: CF.h_formula) (h2mpf: CF.mem_perm_formula option)
(mcp: MCP.mix_formula) (p_vars: CP.spec_var list) (q_vars: CP.spec_var list) : CF.h_formula * CP.formula = 
(match h1mpf,h2mpf with
| Some(memf1), Some(memf2) -> (match h2 with
	| CF.ViewNode {CF.h_formula_view_node = vn2;
		       CF.h_formula_view_arguments = vargs2} ->
		       let case_and_layouts2 = List.combine memf2.CF.mem_formula_guards memf2.CF.mem_formula_field_layout in
               let case_and_values2 = List.combine memf2.CF.mem_formula_guards memf2.CF.mem_formula_field_values in
		       let sublist2 = List.combine q_vars vargs2 in
		       let pure_p = (MCP.pure_of_mix mcp) in
		       let compatible_values2 = List.filter (fun (c,_) ->
		       let after_sbst_guard = CP.subst sublist2 c in		
		       let r,_,_ =  
		       TP.imply_one 101 pure_p after_sbst_guard "ramify_imply" false None in r) case_and_values2 in
		       let compatible_cases2 = List.filter (fun (c,_) ->
		       let after_sbst_guard = CP.subst sublist2 c in		
		       let r,_,_ =  
		       TP.imply_one 12 pure_p after_sbst_guard "ramify_imply" false None in r) case_and_layouts2 in
		       (match h1 with
			| CF.ViewNode {CF.h_formula_view_node = vn1;
				CF.h_formula_view_arguments = vargs1} -> 
				let case_and_layouts1 = List.combine memf1.CF.mem_formula_guards memf1.CF.mem_formula_field_layout in
				let case_and_values1 = List.combine memf1.CF.mem_formula_guards memf1.CF.mem_formula_field_values in
       				let sublist1 = List.combine p_vars vargs1 in
       				let compatible_values1 = List.filter (fun (c,_) ->
       				let after_sbst_guard = CP.subst sublist1 c in		
			       	let r,_,_ =
			       	TP.imply_one 102 pure_p after_sbst_guard "ramify_imply" false None in r) case_and_values1 in
       				let compatible_cases1 = List.filter (fun (c,_) ->
       				let after_sbst_guard = CP.subst sublist1 c in		
			       	let r,_,_ =
			       	TP.imply_one 13 pure_p after_sbst_guard "ramify_imply" false None in r) case_and_layouts1 in
			       	let field_names = List.map (fun (_,(id,_)) -> id ) compatible_cases1 in
			       	let field_names_no_dup = remove_dups field_names in
			       	if List.exists (fun (_,(id,_)) -> (List.mem id field_names_no_dup)) compatible_cases2 
			       	then (if List.exists (fun (_,(_,al2)) -> List.exists (fun(_,(_,al1)) ->
			       		(is_same_field_layout al1 al2)) compatible_cases1
			       		) compatible_cases2
					    then (* Field Layout is Same, Check for Field Values to Ramify *)
                        (if List.exists (fun (_,(_,al2)) -> List.exists (fun(_,(_,al1)) ->
   			   (*let () = print_string("Field Values List1 : "^(string_of_list_f string_of_formula_exp al1)^"\n") in
       		   let () = print_string("Field Values List2 : "^(string_of_list_f string_of_formula_exp al2)^"\n") in
		       let () = if (is_same_field_values al1 al2 pure_p) then print_string("true") else () in*)
			       		  (is_same_field_values al1 al2 pure_p)) compatible_values1
			       		  ) compatible_values2
		       			  	(*let () = print_string("H: "^(string_of_h_formula h1)^"\n") in*)
                              then h1,(CP.mkTrue no_pos)
                            else let compatible_fvs = List.map (fun (_,(_,fl)) -> fl) compatible_values2 in
					             let ramified_cases = List.filter (fun (_,(_,fl)) ->
					               List.exists (fun c -> 
					                 (is_same_field_values c fl pure_p)) compatible_fvs)
					               case_and_values1 in
					             let ch_vars = List.map (fun (g,_) -> CP.fv g) ramified_cases in
					             let ch_vars_lt = remove_dups (List.concat ch_vars) in
					             let old_args = vargs1 in
					             let fresh_args = CP.fresh_spec_vars old_args in
					             let comb = List.combine fresh_args old_args in
					             let comb_with_sublist = List.combine comb sublist1 in
					             let comb_filtered = List.filter (fun ((_,_),(parg,_)) ->
					               List.mem parg ch_vars_lt 
					             ) comb_with_sublist in
					             let comb,_ = List.split comb_filtered in
					             let ramified_subst = List.map 
			                       (fun ((nw,_),(parg,_)) -> (parg,nw)) comb_filtered in
			                     let comb0 = List.map (fun (a,b) -> (b,a)) comb in
					             let new_h1 = CF.h_subst comb0 h1 in
 					             let conjlt1 = List.map (fun (v1,v2) -> 
					               CP.mkEqVar v1 v2 no_pos
					             ) comb0 in
					             let p1 = CP.join_conjunctions conjlt1 in
					             let conjlt2 = List.map (fun (g,_) ->
					               CP.subst ramified_subst g							
					             ) ramified_cases in
					             let p2 = CP.join_conjunctions conjlt2 in
					             let new_p = CP.mkOr p1 p2 None no_pos in
 					             (new_h1,new_p))
					else let compatible_fls = List.map (fun (_,(_,fl)) -> fl) compatible_cases2 in
					let ramified_cases = List.filter (fun (_,(_,fl)) ->
					List.exists (fun c -> 
					(is_same_field_layout c fl) || (is_compatible_field_layout c fl)) compatible_fls)
					case_and_layouts1 in
					let ch_vars = List.map (fun (g,_) -> CP.fv g) ramified_cases in
					let ch_vars_lt = remove_dups (List.concat ch_vars) in
					let old_args = vargs1 in
					let fresh_args = CP.fresh_spec_vars old_args in
					let comb = List.combine fresh_args old_args in
					let comb_with_sublist = List.combine comb sublist1 in
					let comb_filtered = List.filter (fun ((_,_),(parg,_)) ->
					List.mem parg ch_vars_lt 
					) comb_with_sublist in
					let comb,_ = List.split comb_filtered in
					let ramified_subst = List.map 
			                (fun ((nw,_),(parg,_)) -> (parg,nw)) comb_filtered in
			                let comb0 = List.map (fun (a,b) -> (b,a)) comb in
					let new_h1 = CF.h_subst comb0 h1 in
 					let conjlt1 = List.map (fun (v1,v2) -> 
					CP.mkEqVar v1 v2 no_pos
					) comb0 in
					let p1 = CP.join_conjunctions conjlt1 in
					let conjlt2 = List.map (fun (g,_) ->
					CP.subst ramified_subst g							
					) ramified_cases in
					let p2 = CP.join_conjunctions conjlt2 in
					let new_p = CP.mkOr p1 p2 None no_pos in
 					(new_h1,new_p) 
					)
			       	else h1,(CP.mkTrue no_pos)
		       	| _ -> CF.HTrue,(CP.mkTrue no_pos)) (* Shouldn't get here *)
		       			
	| _ ->CF.HTrue,(CP.mkTrue no_pos)) (* Shouldn't get here *)
| Some(memf1), None -> (match h2 with
			| CF.DataNode { CF.h_formula_data_name = dn;
			       		CF.h_formula_data_param_imm = paimm;
                          CF.h_formula_data_arguments = da;} -> 
                        let daexps = List.map (fun c -> CP.Var(c,no_pos)) da in
			       		(match h1 with
			       		| CF.ViewNode {CF.h_formula_view_node = vn;
		       				CF.h_formula_view_arguments = vargs} -> 
		       				let case_and_layouts = 
                              List.combine memf1.CF.mem_formula_guards memf1.CF.mem_formula_field_layout in
                            let case_and_values = 
                              List.combine memf1.CF.mem_formula_guards memf1.CF.mem_formula_field_values in
		       				let sublist = List.combine p_vars vargs in
		       				let pure_p = (MCP.pure_of_mix mcp) in
	                        let compatible_values = List.filter (fun (c,_) ->
		       				let after_sbst_guard = CP.subst sublist c in		
					       	let r,_,_ =
					       	TP.imply_one 103 pure_p after_sbst_guard "ramify_imply" false None in r) case_and_values in
		       				let compatible_cases = List.filter (fun (c,_) ->
		       				let after_sbst_guard = CP.subst sublist c in		
					       	let r,_,_ =
					       	TP.imply_one 14 pure_p after_sbst_guard "ramify_imply" false None in r) case_and_layouts in
					       	if List.exists (fun (_,(id,_)) -> (String.compare id dn == 0)) compatible_cases
						    then (if List.exists (fun (_,(id,al)) -> 
							(is_same_field_layout paimm al)) compatible_cases
							then (* Field Layout is Same Check for Field Values to Ramify *)
		       			      (if List.exists (fun (_,(i_,al)) -> 
       			   (*let () = print_string("Field Values List : "^(string_of_list_f string_of_formula_exp al)^"\n") in
       			   let () = print_string("Data Field Values List : "^(string_of_list_f string_of_formula_exp daexps)^"\n") in
		       			   let () = if (is_same_field_values daexps al pure_p) then print_string("true") else () in*)
		       			       (is_same_field_values daexps al pure_p)) compatible_values
		       			  	(*let () = print_string("H: "^(string_of_h_formula h1)^"\n") in*)
                              then h1,(CP.mkTrue no_pos)
                               else let ramified_cases = List.filter (fun (_,(_,fl)) ->
							     (is_same_field_values daexps fl pure_p) )
							          case_and_values in
							        let ch_vars = List.map (fun (g,_) -> CP.fv g) ramified_cases in
							        let ch_vars_lt = remove_dups (List.concat ch_vars) in
							        let old_args = vargs in
							        let fresh_args = CP.fresh_spec_vars old_args in
					                let comb = List.combine fresh_args old_args in
					                let comb_with_sublist = List.combine comb sublist in
					                let comb_filtered = List.filter (fun ((_,_),(parg,_)) ->
					                List.mem parg ch_vars_lt 
					                ) comb_with_sublist in
					                let comb,_ = List.split comb_filtered in
					                let ramified_subst = List.map 
					                (fun ((nw,_),(parg,_)) -> (parg,nw)) comb_filtered in
					                let comb0 = List.map (fun (a,b) -> (b,a)) comb in
					              	let new_h1 = CF.h_subst comb0 h1 in
 					   		        let conjlt1 = List.map (fun (v1,v2) -> 
							          CP.mkEqVar v1 v2 no_pos
							        ) comb0 in
							        let p1 = CP.join_conjunctions conjlt1 in
							        let conjlt2 = List.map (fun (g,_) ->
							          CP.subst ramified_subst g						
							        ) ramified_cases in
							        let p2 = CP.join_conjunctions conjlt2 in
							        let new_p = CP.mkOr p1 p2 None no_pos in
							(*let () = print_string("\nNew P: "^(string_of_pure_formula new_p)^"\n") in*)
 					   		        (new_h1,new_p) )
							else let ramified_cases = List.filter (fun (_,(_,fl)) ->
							(is_same_field_layout paimm fl) ||(is_compatible_field_layout paimm fl))
							case_and_layouts in
							let ch_vars = List.map (fun (g,_) -> CP.fv g) ramified_cases in
							let ch_vars_lt = remove_dups (List.concat ch_vars) in
							let old_args = vargs in
							let fresh_args = CP.fresh_spec_vars old_args in
					                let comb = List.combine fresh_args old_args in
					                let comb_with_sublist = List.combine comb sublist in
					                let comb_filtered = List.filter (fun ((_,_),(parg,_)) ->
					                List.mem parg ch_vars_lt 
					                ) comb_with_sublist in
					                let comb,_ = List.split comb_filtered in
					                let ramified_subst = List.map 
					                (fun ((nw,_),(parg,_)) -> (parg,nw)) comb_filtered in
					                let comb0 = List.map (fun (a,b) -> (b,a)) comb in
					              	let new_h1 = CF.h_subst comb0 h1 in
 					   		let conjlt1 = List.map (fun (v1,v2) -> 
							CP.mkEqVar v1 v2 no_pos
							) comb0 in
							let p1 = CP.join_conjunctions conjlt1 in
							let conjlt2 = List.map (fun (g,_) ->
							CP.subst ramified_subst g						
							) ramified_cases in
							let p2 = CP.join_conjunctions conjlt2 in
							let new_p = CP.mkOr p1 p2 None no_pos in
							(*let () = print_string("\nNew P: "^(string_of_pure_formula new_p)^"\n") in*)
 					   		(new_h1,new_p)
						)
						else  h1,(CP.mkTrue no_pos)
		       			| _ -> CF.HTrue,(CP.mkTrue no_pos)) (* shouldn't get here *)
			       		
			| _ -> CF.HTrue,(CP.mkTrue no_pos)) (* shouldn't get here *)
| None , Some(memf2) -> 
	(match h2 with
	| CF.ViewNode {CF.h_formula_view_node = vn;
		       CF.h_formula_view_arguments = vargs} -> 
		       let case_and_layouts = List.combine memf2.CF.mem_formula_guards memf2.CF.mem_formula_field_layout in
               let case_and_values =  List.combine memf2.CF.mem_formula_guards memf2.CF.mem_formula_field_values in
		       let sublist = List.combine q_vars vargs in
		       let pure_p = (MCP.pure_of_mix mcp) in
               let compatible_values = List.filter (fun (c,_) ->
		       	let after_sbst_guard = CP.subst sublist c in		
		       	let r,_,_ =  
		       	(*let () = print_string("\nPure :"^(string_of_pure_formula pure_p)^"\n") in
		       	let () = print_string("Case :"^(string_of_pure_formula after_sbst_guard)^"\n") in*)
		       	TP.imply_one 104 pure_p after_sbst_guard "ramify_imply" false None in r) case_and_values in
		       let compatible_cases = List.filter (fun (c,_) ->
		       	let after_sbst_guard = CP.subst sublist c in		
		       	let r,_,_ =  
		       	(*let () = print_string("\nPure :"^(string_of_pure_formula pure_p)^"\n") in
		       	let () = print_string("Case :"^(string_of_pure_formula after_sbst_guard)^"\n") in*)
		       	TP.imply_one 15 pure_p after_sbst_guard "ramify_imply" false None in r) case_and_layouts in
		       (match h1 with
		       	| CF.DataNode { CF.h_formula_data_name = dn;
                        CF.h_formula_data_arguments = da;
			       		CF.h_formula_data_param_imm = paimm} -> 
                    let daexps = List.map (fun c -> CP.Var(c,no_pos)) da in
			       		if List.exists (fun (_,(id,_)) -> (String.compare id dn == 0)) compatible_cases
					then			      
		       			 (if List.exists (fun (_,(i_,al)) -> 
		       			   (*let () = print_string("Ann List : "^(string_of_list_f string_of_imm al)^"\n") in
		       			   let () = print_string("Data Ann List : "^(string_of_list_f string_of_imm paimm)^"\n") in
		       			   let () = if (is_same_field_layout paimm al) then print_string("true") else () in*)
		       			   (is_same_field_layout paimm al)) compatible_cases 
		       			  then (* Field Layout is Same Check for Field Values to Ramify *)
		       			      (if List.exists (fun (_,(i_,al)) -> 
       			   (*let () = print_string("Field Values List : "^(string_of_list_f string_of_formula_exp al)^"\n") in
       			   let () = print_string("Data Field Values List : "^(string_of_list_f string_of_formula_exp daexps)^"\n") in
		       			   let () = if (is_same_field_values daexps al pure_p) then print_string("true") else () in*)
		       			       (is_same_field_values daexps al pure_p)) compatible_values
		       			  	(*let () = print_string("H: "^(string_of_h_formula h1)^"\n") in*)
                              then h1,(CP.mkTrue no_pos)
                              else let old_args = da in
							       let fresh_args = CP.fresh_spec_vars old_args in
					                let comb = List.combine old_args fresh_args in
		                          	let new_h1 = CF.h_subst comb h1 in
							(*let () = print_string("\nNew P: "^(string_of_pure_formula new_p)^"\n") in*)
 					   		        (new_h1,(CP.mkTrue no_pos))
                               )
		       			  else 
	       			 	   (let old_args = CF.get_node_args h1 in
					   let fresh_args = CP.fresh_spec_vars old_args in
					   let comb = List.combine old_args fresh_args in
					   let comb_with_paimm = List.combine comb paimm in
					   let comb_filtered = List.filter (fun (_,c) -> CP.isMutable c) comb_with_paimm in
					   let comb,_ = List.split comb_filtered in
					   let new_h1 = CF.h_subst comb h1 in
					   (*let () = print_string("New H: "^(string_of_h_formula new_h1)^"\n") in*)
		       			   new_h1,(CP.mkTrue no_pos))
		       			  )
		       			else h1,(CP.mkTrue no_pos)
			| _ -> CF.HTrue,(CP.mkTrue no_pos))	 (* Shouldn't get here *)		       
	| _ -> CF.HTrue,(CP.mkTrue no_pos))	 (* Shouldn't get here *)	
| None , None -> 
	(match h1 with
	| CF.DataNode {CF.h_formula_data_param_imm = paimm;} -> 
	if String.compare (x_add CF.get_node_name 7 h1) (x_add CF.get_node_name 8 h2) == 0 then
		let old_args = CF.get_node_args h1 in
		let new_args = CF.get_node_args h2 in
		let h1_var = CF.get_node_var h1 in
		let h2_var = CF.get_node_var h2 in
		let fresh_args = CP.fresh_spec_vars old_args in
		let comb1 = List.combine fresh_args new_args in
		let comb2 = List.combine fresh_args old_args in
		let comb = List.combine comb1 comb2 in
		let comb_with_paimm = List.combine comb paimm in
		let comb_filtered = List.filter (fun (_,c) -> CP.isMutable c) comb_with_paimm in
		let comb,_ = List.split comb_filtered in
		let _,lst = List.split comb in
		let fr,ol = List.split lst in
		let new_h1 = CF.h_subst (List.combine ol fr) h1 in
		let conjlt = List.map (fun ((v1,v2),(v3,v4)) -> 
		let p1  = CP.mkEqVar v1 v2 no_pos in
		let p2  = CP.mkEqVar v3 v4 no_pos in
		let p = CP.mkOr p1 p2 None no_pos in
		p
		) comb in
		let new_p = CP.join_conjunctions conjlt in
		let var_p = if (CP.is_primed h2_var) then 
		CP.mkOr (CP.mkEqVar (CP.to_primed h1_var) h1_var no_pos) (CP.mkEqVar (CP.to_primed h1_var) h2_var no_pos) None no_pos 
		else CP.mkTrue no_pos in
		let new_p = CP.mkAnd new_p var_p no_pos in	
		new_h1,new_p
	else h1,(CP.mkTrue no_pos)	
	| _ -> CF.HTrue,(CP.mkTrue no_pos)) (* Shouldn't get here *)
	
	
)

let ramify_star (p: CF.h_formula) (ql: CF.h_formula list) (vl:C.view_decl list) (mcp: MCP.mix_formula) : CF.h_formula * CP.formula = 
(*let () = print_string("Ramification :"^ (string_of_list_f string_of_h_formula ql)^ "\n") in*)
match p with
	| CF.DataNode {CF.h_formula_data_name = name;
                       CF.h_formula_data_node = dn;
                       CF.h_formula_data_imm = imm;
                       CF.h_formula_data_arguments = dargs;
                       CF.h_formula_data_pos = pos} -> 
                       if(CP.isMutable imm) then
                       List.fold_left (fun (h,f) q  -> 
		       let q_mpf, q_vars  = 
		       if (CF.is_view q) then
		       let q_vdef = x_add C.look_up_view_def_raw 21 vl (x_add CF.get_node_name 9 q) in
		       let q_viewvars = q_vdef.C.view_vars in
		       q_vdef.C.view_mem,q_viewvars 
		       else None,[] in
		       let new_p,f2 = ramify_star_one h None q q_mpf mcp [] q_vars in
		       let new_f = CP.mkAnd f f2 pos in
		       (new_p,new_f)) (p,(CP.mkTrue no_pos)) ql
		       else CF.HTrue,(CP.mkTrue no_pos)		    
	| CF.ViewNode {CF.h_formula_view_node = vn;
		       CF.h_formula_view_name = name;
		       CF.h_formula_view_imm = imm;
		       CF.h_formula_view_arguments = vargs;
		       CF.h_formula_view_pos = pos} -> 
		       let p_vdef = x_add C.look_up_view_def_raw 22 vl name in
		       let p_mpf = p_vdef.C.view_mem in
		       let p_vars = p_vdef.C.view_vars in
		       if(CP.isMutable imm) then
		       List.fold_left (fun (h,f) q -> 
		       let q_mpf,q_vars = 
		       if (CF.is_view q) then
		       let q_vdef = x_add C.look_up_view_def_raw 23 vl (x_add CF.get_node_name 10 q) in
		       let q_vars = q_vdef.C.view_vars in
		       q_vdef.C.view_mem, q_vars
		       else None,[] in  
		       let new_p,f2 = ramify_star_one h p_mpf q q_mpf mcp p_vars q_vars in
		       let new_f = CP.mkAnd f f2 pos in
		       (new_p,new_f)) (p,(CP.mkTrue no_pos)) ql
		       else CF.HTrue,(CP.mkTrue no_pos)
        | _ -> p,(CP.mkTrue no_pos)

let ramify_phase = ramify_star

let ramify_conj = ramify_star

let ramify_conjconj = ramify_star

let ramify_conjstar = ramify_star

let frame_after_ramification (h1:CF.h_formula) (h2:CF.h_formula) pos (al1:aliasing_scenario) (al2:aliasing_scenario) 
: CF.h_formula = 
match al1,al2 with
  | Not_Aliased, Not_Aliased -> CF.mkStarH h1 h2 pos
  | May_Aliased, May_Aliased -> CF.mkConjH h1 h2 pos
  | Must_Aliased, Must_Aliased -> CF.mkConjConjH h1 h2 pos
  | Partial_Aliased, Partial_Aliased -> CF.mkConjStarH h1 h2 pos
(*| May_Aliased, _ -> CF.mkConjH h1 h2 pos
  | _ ,May_Aliased -> CF.mkConjH h1 h2 pos*)
  | _ , _ -> CF.mkStarH h1 h2 pos

let rec ramify_starminus_in_h_formula (f: CF.h_formula) (vl:C.view_decl list) (aset: CP.spec_var list list) (fl: CF.h_formula list)
func (mcp: MCP.mix_formula ) : CF.h_formula * CP.formula * aliasing_scenario = 
  if not (contains_starminus f) then f,(CP.mkTrue no_pos),Not_Aliased else 
  let () = Globals.ramification_entailments := !Globals.ramification_entailments + 1 in
  (*let () = print_string("Ramification :"^ (string_of_h_formula f)^ "\n") in*)
    match f with
      | CF.Star {CF.h_formula_star_h1 = h1;
                 CF.h_formula_star_h2 = h2;
                 CF.h_formula_star_pos = pos } ->  
        let res_h1,res_p1,al1 = ramify_starminus_in_h_formula h1 vl aset fl ramify_star mcp in
        let res_h2,res_p2,al2 = ramify_starminus_in_h_formula h2 vl aset fl ramify_star mcp in           
    let res_h = frame_after_ramification res_h1 res_h2 pos al1 al2 in 
	let res_p = CP.mkAnd res_p1 res_p2 pos in
	res_h,res_p,Not_Aliased
      | CF.Conj{CF.h_formula_conj_h1 = h1;
		CF.h_formula_conj_h2 = h2;
	        CF.h_formula_conj_pos = pos} ->
        let res_h1,res_p1,al1 = ramify_starminus_in_h_formula h1 vl aset fl ramify_conj mcp in
        let res_h2,res_p2,al2 = ramify_starminus_in_h_formula h2 vl aset fl ramify_conj mcp in           
    let res_h = frame_after_ramification res_h1 res_h2 pos al1 al2 in 
	let res_p = CP.mkAnd res_p1 res_p2 pos in
	res_h,res_p,May_Aliased
      | CF.ConjStar{CF.h_formula_conjstar_h1 = h1;
		CF.h_formula_conjstar_h2 = h2;
	        CF.h_formula_conjstar_pos = pos} ->
        let res_h1,res_p1,al1 = ramify_starminus_in_h_formula h1 vl aset fl ramify_conjstar mcp in
        let res_h2,res_p2,al2 = ramify_starminus_in_h_formula h2 vl aset fl ramify_conjstar mcp in           
	let res_h = CF.mkConjStarH res_h1 res_h2 pos in
	let res_p = CP.mkAnd res_p1 res_p2 pos in
	res_h,res_p,Partial_Aliased
      | CF.ConjConj{CF.h_formula_conjconj_h1 = h1;
		CF.h_formula_conjconj_h2 = h2;
	        CF.h_formula_conjconj_pos = pos} ->
        let res_h1,res_p1,al1 = ramify_starminus_in_h_formula h1 vl aset fl ramify_conjconj mcp in
        let res_h2,res_p2,al2 = ramify_starminus_in_h_formula h2 vl aset fl ramify_conjconj mcp in           
	let res_h = CF.mkConjConjH res_h1 res_h2 pos in
	let res_p = CP.mkAnd res_p1 res_p2 pos in
	res_h,res_p,Must_Aliased		 	        
      | CF.Phase {CF.h_formula_phase_rd = h1;
		CF.h_formula_phase_rw = h2;
	        CF.h_formula_phase_pos = pos} ->
        let res_h1,res_p1,al1 = ramify_starminus_in_h_formula h1 vl aset fl ramify_phase mcp in
        let res_h2,res_p2,al2 = ramify_starminus_in_h_formula h2 vl aset fl ramify_phase mcp in           
	let res_h = CF.mkPhaseH res_h1 res_h2 pos in
	let res_p = CP.mkAnd res_p1 res_p2 pos in
	res_h,res_p,Not_Aliased
     | CF.StarMinus({CF.h_formula_starminus_h1 = h1;
	CF.h_formula_starminus_h2 = h2;
    CF.h_formula_starminus_aliasing = al;
	CF.h_formula_starminus_pos = pos}) -> 
	if (CF.is_data h2) || (CF.is_view h2) then 
	let aset_sv  = Csvutil.get_aset aset (CF.get_node_var h2) in
	let ramify_list = List.filter (fun c -> let sp_c = (CF.get_node_var c) in
	(*let () = print_string("Svar :"^(string_of_spec_var sp_c)^"\n") in*)
	((CP.mem sp_c aset_sv) || (CP.eq_spec_var (CF.get_node_var h2) sp_c))) fl in
	let res_h1, res_p1 = if (List.length ramify_list) > 0 then func h1 ramify_list vl mcp else f,(CP.mkTrue no_pos) in
	res_h1,res_p1,al
	else CF.HTrue,(CP.mkTrue no_pos),al	
      | _ -> f,(CP.mkTrue no_pos),Not_Aliased

let ramify_starminus_in_h_formula (f: CF.h_formula) (vl:C.view_decl list) (aset: CP.spec_var list list) (fl: CF.h_formula list)
func (mcp: MCP.mix_formula ) : CF.h_formula * CP.formula * aliasing_scenario = 
  let pr = string_of_h_formula in
  let pr2 = (fun (a,b,c) -> (pr_pair string_of_h_formula string_of_pure_formula (a,b) )) in
  Debug.no_1 "ramify_starminus_in_h_formula" pr pr2 (fun c -> ramify_starminus_in_h_formula c vl aset fl func mcp) f
	
let rec ramify_starminus_in_formula (cf: CF.formula) (vl:C.view_decl list): CF.formula =
 let () = Globals.total_entailments := !Globals.total_entailments + 1 in
  if not (!Globals.allow_mem) then cf else
  match cf with
    | CF.Base f   -> 
        let old_p = f.CF.formula_base_pure in
        let fl = split_into_list f.CF.formula_base_heap in
        let new_h,new_p,_ = 
    	ramify_starminus_in_h_formula f.CF.formula_base_heap vl (Csvutil.comp_aliases old_p) fl ramify_star old_p
    	in 
    	let new_mcp = MCP.merge_mems f.CF.formula_base_pure (MCP.mix_of_pure new_p) true in
    	CF.Base { f with
        CF.formula_base_heap = new_h;       
	CF.formula_base_pure = new_mcp;}
    | CF.Or f     -> CF.Or { f with 
        CF.formula_or_f1 = ramify_starminus_in_formula f.CF.formula_or_f1 vl; 
        CF.formula_or_f2 = ramify_starminus_in_formula f.CF.formula_or_f2 vl; }
    | CF.Exists f -> 
    	let qevars = f.CF.formula_exists_qvars in 
    	let h = f.CF.formula_exists_heap in
    	let mp = f.CF.formula_exists_pure in
        let fl = split_into_list h in
    	let new_h,new_p,_ = 
    	ramify_starminus_in_h_formula h vl (Csvutil.comp_aliases mp) fl ramify_star mp
    	in
 	let new_mcp = MCP.merge_mems mp (MCP.mix_of_pure new_p) true in
    	CF.Exists { f with
    	CF.formula_exists_qvars = qevars;
        CF.formula_exists_heap = new_h;
        CF.formula_exists_pure = new_mcp;}


let get_neq_for_ramify (h:CF.h_formula) (r:CF.h_formula) (p:CP.formula) vl pos : CP.formula = 
if (CF.is_data h) then
        if (CF.is_data r) then
     	let p1 = CP.mkNeqVar (CF.get_node_var r) (CF.get_node_var h) pos in
	CP.mkAnd p1 p pos
	else (* r is a view *) 
        let vdef = x_add C.look_up_view_def_raw 24 vl (x_add CF.get_node_name 11 r) in
        let args = vdef.C.view_vars in
        let rargs = (CF.get_node_args r) in
        let sst = List.combine args rargs in 
        let mpf = Gen.unsome vdef.C.view_mem in (* get the memory exp of the view *) 
        let mexp = CP.e_apply_subs sst mpf.CF.mem_formula_exp in
        let p1 = CP.BForm((CP.BagNotIn((CF.get_node_var h),mexp,pos),None),None) in
        CP.mkAnd p1 p pos
else if (CF.is_view h) then
	let vdef = x_add C.look_up_view_def_raw 25 vl (x_add CF.get_node_name 12 h) in
	let mpf = Gen.unsome vdef.C.view_mem in
	let args = vdef.C.view_vars in
        let hargs = (CF.get_node_args h) in
        let sst = List.combine args hargs in 
	let mexp = CP.e_apply_subs sst mpf.CF.mem_formula_exp in	          
        if(CF.is_data r) then
	let p1 = CP.BForm((CP.BagNotIn((CF.get_node_var r),mexp,pos),None),None) in
        CP.mkAnd p1 p pos
        else (* r is a view *) 
	let vdef_r = x_add C.look_up_view_def_raw 26 vl (x_add CF.get_node_name 13 r) in
	let mpf_r = Gen.unsome vdef_r.C.view_mem in
        let args_r = vdef_r.C.view_vars in
        let rargs_r = (CF.get_node_args r) in
        let sst_r = List.combine args_r rargs_r in
        let mexp_r = CP.e_apply_subs sst_r mpf_r.CF.mem_formula_exp in (* get the memory exp of the view *) 
        let bagexp = CP.BagIntersect(mexp::[mexp_r],pos) in
        let emp_bag = CP.Bag([],pos) in
        let p1 = CP.mkNeqExp bagexp emp_bag pos in
        CP.mkAnd p1 p pos 
else p

        
(* Generate basic cases to Ramify a complex heap in formula h *- r *)
let rec ramify_complex_heap (h:CF.h_formula) (r:CF.h_formula) (p:CP.formula) (vl:C.view_decl list) :
(CF.h_formula * CP.formula) list = 
let ct = (CP.mkTrue no_pos) in
match h with
| CF.Star {CF.h_formula_star_h1 = h1;
           CF.h_formula_star_h2 = h2;
           CF.h_formula_star_pos = pos } 
| CF.ConjStar{CF.h_formula_conjstar_h1 = h1;
	CF.h_formula_conjstar_h2 = h2;
        CF.h_formula_conjstar_pos = pos}                            
| CF.Conj{CF.h_formula_conj_h1 = h1;
	CF.h_formula_conj_h2 = h2;
        CF.h_formula_conj_pos = pos} 
| CF.ConjConj{CF.h_formula_conjconj_h1 = h1;
	CF.h_formula_conjconj_h2 = h2;
        CF.h_formula_conjconj_pos = pos}
| CF.Phase {CF.h_formula_phase_rd = h1;
	CF.h_formula_phase_rw = h2;
        CF.h_formula_phase_pos = pos} -> 
        let lp = get_neq_for_ramify h2 r p vl pos in
        let rp = get_neq_for_ramify h1 r p vl pos in
        let res_lst1 = ramify_complex_heap h1 r lp vl in
        let res_lst2 = ramify_complex_heap h2 r rp vl in
        let res_lst = List.map (fun (h2,p2) -> 
	        List.map (fun (h1,p1) -> let res_h = CF.mkStarH h1 h2 pos in
	        	let res_p = CP.mkAnd p1 p2 pos in (res_h,res_p)
	         ) res_lst1 ) res_lst2 in 
        let res_lst = List.flatten res_lst in      
	res_lst
| CF.StarMinus({CF.h_formula_starminus_h1 = h1;
	CF.h_formula_starminus_h2 = h2;
	CF.h_formula_starminus_pos = pos}) -> 
	if (CF.is_data h2) || (CF.is_view h2) then 
	List.flatten (List.map (fun (h,p) -> ramify_complex_heap h r p vl) (ramify_complex_heap h1 h2 p vl))
	else [CF.HTrue,ct]
| CF.DataNode {CF.h_formula_data_name = name;
     CF.h_formula_data_node = dn;
     CF.h_formula_data_imm = imm;
     CF.h_formula_data_arguments = dargs;
     CF.h_formula_data_pos = pos} -> 
     (match r with 
     |  CF.DataNode {CF.h_formula_data_name = rname;
     	CF.h_formula_data_node = rdn;
     	CF.h_formula_data_imm = rimm;
     	CF.h_formula_data_arguments = rdargs;
     	CF.h_formula_data_pos = rpos} -> 
     	if(String.compare name rname == 0) then
     	let first_case_h = CF.HEmp in (* h = r *)
     	let first_case_p = CP.mkEqVar dn rdn pos in
     	let combined_args = List.combine dargs rdargs in
     	let conj_list = List.map (fun (v1,v2) -> CP.mkEqVar v1 v2 pos) combined_args in
     	let first_case_p = CP.mkAnd first_case_p (CP.join_conjunctions conj_list) pos in
     	let second_case_h = h in (* h != r *)
     	let second_case_p = CP.mkNeqVar dn rdn rpos in
     	let first_case_p = CP.mkAnd first_case_p p pos in
     	let second_case_p = CP.mkAnd second_case_p p rpos in
     	[(first_case_h,first_case_p)]@[(second_case_h,second_case_p)]
     	else [(h,p)]
     |  CF.ViewNode {CF.h_formula_view_node = rvn;
        CF.h_formula_view_name = rname;
        CF.h_formula_view_imm = rimm;
        CF.h_formula_view_arguments = rvargs;
        CF.h_formula_view_pos = rpos} -> 
        let vdef = x_add C.look_up_view_def_raw 27 vl rname in
        let args = vdef.C.view_vars in
        let sst = List.combine args rvargs in 
        let mpf = Gen.unsome vdef.C.view_mem in
        let mpf_mexp = CP.e_apply_subs sst mpf.CF.mem_formula_exp in
        let mpf_fl = mpf.CF.mem_formula_field_layout in
        if List.exists (fun (id,_) -> String.compare id name == 0) mpf_fl then
        let first_case_h = CF.HEmp in (* h = r *)       
     	let first_case_p = CP.BForm((CP.BagIn(dn,mpf_mexp,pos),None),None) in
     	let second_case_h = h in (* h != r *)
    	let second_case_p = CP.BForm((CP.BagNotIn(dn,mpf_mexp,pos),None),None) in
     	let first_case_p = CP.mkAnd first_case_p p pos in
     	let second_case_p = CP.mkAnd second_case_p p rpos in
     	[(first_case_h,first_case_p)]@[(second_case_h,second_case_p)]
        else [(h,p)]            
     | _ -> [])               			
| CF.ViewNode {CF.h_formula_view_node = vn;
     CF.h_formula_view_name = name;
     CF.h_formula_view_imm = imm;
     CF.h_formula_view_arguments = vargs;
     CF.h_formula_view_pos = pos} ->
     let vdef = x_add C.look_up_view_def_raw 28 vl name in
     let mpf = Gen.unsome vdef.C.view_mem in
     let args = vdef.C.view_vars in
     let sst = List.combine args vargs in
     let mpf_mexp = CP.e_apply_subs sst mpf.CF.mem_formula_exp in
     let mpf_fl = mpf.CF.mem_formula_field_layout in
     (match r with 
     |  CF.DataNode {CF.h_formula_data_name = rname;
     	CF.h_formula_data_node = rdn;
     	CF.h_formula_data_imm = rimm;
     	CF.h_formula_data_arguments = rdargs;
     	CF.h_formula_data_pos = rpos} -> 
     	if List.exists (fun (id,_) -> String.compare id rname == 0) mpf_fl then
     	let first_case_h = CF.mkStarMinusH h r Not_Aliased pos 57 in (* Will need a matching lemma for a cyclic proof *)
     	let first_case_p = CP.BForm((CP.BagIn(rdn,mpf_mexp,pos),None),None) in   
     	let second_case_h = h in (* h != r *)
    	let second_case_p = CP.BForm((CP.BagNotIn(rdn,mpf_mexp,pos),None),None) in  	
     	let first_case_p = CP.mkAnd first_case_p p pos in
     	let second_case_p = CP.mkAnd second_case_p p rpos in
     	[(first_case_h,first_case_p)]@[(second_case_h,second_case_p)]
     	else [(h,p)] 
     |  CF.ViewNode {CF.h_formula_view_node = rvn;
        CF.h_formula_view_name = rname;
        CF.h_formula_view_imm = rimm;
        CF.h_formula_view_arguments = rvargs;
        CF.h_formula_view_pos = rpos} ->
        let vdef_r = x_add C.look_up_view_def_raw 29 vl name in
	let mpf_r = Gen.unsome vdef_r.C.view_mem in
        let args_r = vdef_r.C.view_vars in
	let sst_r = List.combine args_r rvargs in
	let mpf_r_mexp = CP.e_apply_subs sst_r mpf_r.CF.mem_formula_exp in
	let mpf_r_fl = mpf_r.CF.mem_formula_field_layout in
	let check_list = List.map (fun (id,_) -> id) mpf_r_fl in
    	if List.exists (fun (id,_) -> List.mem id check_list) mpf_fl then
        let bagexp = CP.BagIntersect(mpf_mexp::[mpf_r_mexp],pos) in
        let emp_bag = CP.Bag([],pos) in
    	let first_case_h = CF.mkStarMinusH h r Not_Aliased pos 59 in (* Will need a matching lemma for a cyclic proof *)
        let first_case_p = CP.mkNeqExp bagexp emp_bag pos in    	
       	let second_case_h = h in (* h != r *)
        let second_case_p = CP.mkEqExp bagexp emp_bag pos in       	
     	let first_case_p = CP.mkAnd first_case_p p pos in
     	let second_case_p = CP.mkAnd second_case_p p rpos in
     	[(first_case_h,first_case_p)]@[(second_case_h,second_case_p)] 
    	else [(h,p)]          
     | _ -> [])              
| _ -> []         


let rec ramify_unfolded_heap (h: CF.h_formula) (p: CP.formula) vl : (CF.h_formula * CP.formula) list =
  if not (contains_starminus h) then [h,(CP.mkTrue no_pos)] else
    match h with
      | CF.Star {CF.h_formula_star_h1 = h1;
                 CF.h_formula_star_h2 = h2;
                 CF.h_formula_star_pos = pos } ->  
        let res_lst1 = ramify_unfolded_heap h1 p vl in
        let res_lst2 = ramify_unfolded_heap h2 p vl in
        let res_lst = List.map (fun (h2,p2) -> 
	        List.map (fun (h1,p1) -> let res_h = CF.mkStarH h1 h2 pos in
	        	let res_p = CP.mkAnd p1 p2 pos in (res_h,res_p)
	         ) res_lst1 ) res_lst2 in 
        let res_lst = List.flatten res_lst in      
	res_lst
      | CF.Conj{CF.h_formula_conj_h1 = h1;
		CF.h_formula_conj_h2 = h2;
	        CF.h_formula_conj_pos = pos} ->
        let res_lst1 = ramify_unfolded_heap h1 p vl in
        let res_lst2 = ramify_unfolded_heap h2 p vl in
        let res_lst = List.map (fun (h2,p2) -> 
	        List.map (fun (h1,p1) -> let res_h = CF.mkConjH h1 h2 pos in
	        	let res_p = CP.mkAnd p1 p2 pos in (res_h,res_p)
	         ) res_lst1 ) res_lst2 in 
        let res_lst = List.flatten res_lst in      
	res_lst
      | CF.ConjStar{CF.h_formula_conjstar_h1 = h1;
		CF.h_formula_conjstar_h2 = h2;
	        CF.h_formula_conjstar_pos = pos} ->
        let res_lst1 = ramify_unfolded_heap h1 p vl in
        let res_lst2 = ramify_unfolded_heap h2 p vl in
        let res_lst = List.map (fun (h2,p2) -> 
	        List.map (fun (h1,p1) -> let res_h = CF.mkConjStarH h1 h2 pos in
	        	let res_p = CP.mkAnd p1 p2 pos in (res_h,res_p)
	         ) res_lst1 ) res_lst2 in 
        let res_lst = List.flatten res_lst in      
	res_lst
      | CF.ConjConj{CF.h_formula_conjconj_h1 = h1;
		CF.h_formula_conjconj_h2 = h2;
	        CF.h_formula_conjconj_pos = pos} ->
        let res_lst1 = ramify_unfolded_heap h1 p vl in
        let res_lst2 = ramify_unfolded_heap h2 p vl in
        let res_lst = List.map (fun (h2,p2) -> 
	        List.map (fun (h1,p1) -> let res_h = CF.mkConjConjH h1 h2 pos in
	        	let res_p = CP.mkAnd p1 p2 pos in (res_h,res_p)
	         ) res_lst1 ) res_lst2 in 
        let res_lst = List.flatten res_lst in      
	res_lst		 	        
      | CF.Phase {CF.h_formula_phase_rd = h1;
		CF.h_formula_phase_rw = h2;
	        CF.h_formula_phase_pos = pos} ->
        let res_lst1 = ramify_unfolded_heap h1 p vl in
        let res_lst2 = ramify_unfolded_heap h2 p vl in
        let res_lst = List.map (fun (h2,p2) -> 
	        List.map (fun (h1,p1) -> let res_h = CF.mkPhaseH h1 h2 pos in
	        	let res_p = CP.mkAnd p1 p2 pos in (res_h,res_p)
	         ) res_lst1 ) res_lst2 in 
        let res_lst = List.flatten res_lst in      
	res_lst
     | CF.StarMinus({CF.h_formula_starminus_h1 = h1;
	CF.h_formula_starminus_h2 = h2;
	CF.h_formula_starminus_pos = pos}) -> 
	if (CF.is_data h2) || (CF.is_view h2) then 
        ramify_complex_heap h1 h2 p vl
	else [CF.HTrue,(CP.mkTrue no_pos)]	
      | _ -> [h,(CP.mkTrue no_pos)]

let rec ramify_unfolded_formula (cf:CF.formula) vl : CF.formula = 
  match cf with
    | CF.Or f -> 
             let f1 = f.CF.formula_or_f1 in
             let f2 = f.CF.formula_or_f2 in
    	     CF.Or {f with 
	     CF.formula_or_f1 = (ramify_unfolded_formula f1 vl);
	     CF.formula_or_f2 = (ramify_unfolded_formula f2 vl)}
    | CF.Base f ->
    		let pos = f.CF.formula_base_pos in
    		let h,mcp,vp,fl,t,a = CF.split_components cf in
    		(*let p = MCP.pure_of_mix mcp in*)
    		let ramify_cases = ramify_unfolded_heap h (CP.mkTrue no_pos) vl in
    		let or_list = List.map (fun (h,rp) -> let p = MCP.merge_mems mcp (MCP.mix_of_pure rp) true in
    			CF.mkBase h p vp t fl a pos) ramify_cases in
    		CF.disj_of_list or_list pos
    | CF.Exists f ->
		let pos = f.CF.formula_exists_pos in
    		let h,mcp,vp,fl,t,a = CF.split_components cf in
    		let qvars = f.CF.formula_exists_qvars in
    		(*let p = MCP.pure_of_mix mcp in*)
    		let ramify_cases = ramify_unfolded_heap h (CP.mkTrue no_pos) vl in
    		let or_list = List.map (fun (h,rp) -> let p = MCP.merge_mems mcp (MCP.mix_of_pure rp) true in
    			CF.mkExists qvars h p vp t fl a pos) ramify_cases in
    		CF.disj_of_list or_list pos
    		
let rec remove_accs_from_heap (h: CF.h_formula) : CF.h_formula * CP.formula = 
match h with
  | CF.Phase({CF.h_formula_phase_rd = h1;
	CF.h_formula_phase_rw = h2;
	CF.h_formula_phase_pos = pos}) ->
	let h1,p1 = (remove_accs_from_heap h1) in
	let h2,p2 = (remove_accs_from_heap h2) in
	let p = CP.mkAnd p1 p2 pos in
	CF.mkPhaseH h1 h2 pos,p	
  | CF.Star({CF.h_formula_star_h1 = h1;
	CF.h_formula_star_h2 = h2;
	CF.h_formula_star_pos = pos}) ->
	let h1,p1 = (remove_accs_from_heap h1) in
	let h2,p2 = (remove_accs_from_heap h2) in
	let p = CP.mkAnd p1 p2 pos in
	CF.mkStarH h1 h2 pos,p	
  | CF.Conj({CF.h_formula_conj_h1 = h1;
	CF.h_formula_conj_h2 = h2;
	CF.h_formula_conj_pos = pos}) ->
	let h1,p1 = (remove_accs_from_heap h1) in
	let h2,p2 = (remove_accs_from_heap h2) in
	let p = CP.mkAnd p1 p2 pos in
	CF.mkConjH h1 h2 pos,p	
  | CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
	CF.h_formula_conjstar_h2 = h2;
	CF.h_formula_conjstar_pos = pos}) ->
	let h1,p1 = (remove_accs_from_heap h1) in
	let h2,p2 = (remove_accs_from_heap h2) in
	let p = CP.mkAnd p1 p2 pos in
	CF.mkConjStarH h1 h2 pos,p	
  | CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
	CF.h_formula_conjconj_h2 = h2;
	CF.h_formula_conjconj_pos = pos}) -> 
	let h1,p1 = (remove_accs_from_heap h1) in
	let h2,p2 = (remove_accs_from_heap h2) in
	let p = CP.mkAnd p1 p2 pos in
	CF.mkConjConjH h1 h2 pos,p
  | CF.DataNode _
  | CF.ViewNode _ -> let imm = CF.get_node_imm h in
  			if CP.isAccs imm 
  			then let p = (CP.mkNeqNull (CF.get_node_var h) no_pos) in
  				CF.HEmp,p
  			else h,(CP.mkTrue no_pos)
  | _ -> h,(CP.mkTrue no_pos)

let rec remove_accs_from_formula (cf:CF.formula)  : CF.formula = 
  match cf with
    | CF.Or f -> 
             let f1 = f.CF.formula_or_f1 in
             let f2 = f.CF.formula_or_f2 in
    	     CF.Or {f with 
	     CF.formula_or_f1 = (remove_accs_from_formula f1);
	     CF.formula_or_f2 = (remove_accs_from_formula f2)}
    | CF.Base f ->
    		let pos = f.CF.formula_base_pos in
    		let h,mcp,vp,fl,t,a = CF.split_components cf in
    		(*let p = MCP.pure_of_mix mcp in*)
    		let h,new_p = remove_accs_from_heap h in
    		let mcp = MCP.merge_mems (MCP.mix_of_pure new_p) mcp true in
    		CF.mkBase h mcp vp t fl a pos
    | CF.Exists f ->
		let pos = f.CF.formula_exists_pos in
    		let h,mcp,vp,fl,t,a = CF.split_components cf in
    		let qvars = f.CF.formula_exists_qvars in
    		(*let p = MCP.pure_of_mix mcp in*)
    		let h,new_p = remove_accs_from_heap h in
    		let mcp = MCP.merge_mems (MCP.mix_of_pure new_p) mcp true in
 		CF.mkExists qvars h mcp vp t fl a pos	

let rec e_apply_subs sst e =
match sst with
  | [] -> e
  | a::rest -> e_apply_subs rest (IP.e_apply_one a e) 

let rec infer_mem_from_heap (hf: IF.h_formula) (prog:I.prog_decl) 
: IP.exp * ((ident * (IP.ann list)) list) * ((ident * (IP.exp list)) list) = 
match hf with
  | IF.Conj ({IF.h_formula_conj_h1 = h1; 
	IF.h_formula_conj_h2 = h2; 
	IF.h_formula_conj_pos = pos})      
  | IF.ConjStar ({IF.h_formula_conjstar_h1 = h1; 
	IF.h_formula_conjstar_h2 = h2; 
	IF.h_formula_conjstar_pos = pos}) 
  | IF.ConjConj ({IF.h_formula_conjconj_h1 = h1; 
	IF.h_formula_conjconj_h2 = h2; 
	IF.h_formula_conjconj_pos = pos})
  | IF.Phase ({IF.h_formula_phase_rd = h1; 
	IF.h_formula_phase_rw = h2; 
	IF.h_formula_phase_pos = pos}) 
  | IF.Star ({IF.h_formula_star_h1 = h1; 
	IF.h_formula_star_h2 = h2; 
	IF.h_formula_star_pos = pos}) -> 
      let b1,fl1,fv1 = (infer_mem_from_heap h1 prog) in
      let b2,fl2,fv2 = (infer_mem_from_heap h2 prog) in
      IP.BagUnion(b1::[b2],pos),fl1@fl2,fv1@fv2
  | IF.HeapNode ({h_formula_heap_node = x; 
	IF.h_formula_heap_name = c; 
	IF.h_formula_heap_arguments = args;
    IF.h_formula_heap_imm_param  = annl;
	IF.h_formula_heap_pos = pos}) -> 
     (try
        let vdef = I.look_up_view_def_raw 11 prog.I.prog_view_decls c in
        let view_vars = List.map (fun c ->(c,Unprimed)) vdef.I.view_vars in 
        let new_args = List.map (fun c -> match c with 
          | IP.Var((i,p),_) -> (i,p)
          | _ -> raise Not_found) args in
        let sublst = List.combine view_vars new_args in
        let view_mem = vdef.I.view_mem in
        match view_mem with
          | Some a -> let mexp = e_apply_subs sublst a.IF.mem_formula_exp in (mexp , [],[])
          | None -> raise Not_found
     with
      | Not_found -> let args_annl = List.combine args annl in
                     let new_annl = List.map (fun (exp,ann) -> 
                       match ann with
                         | Some a -> a
                         | None -> (match exp with
                             | IP.Var((id,p),_)  -> 
                                 if List.length (IP.anon_var (id,p)) == 0 
                                 then IP.ConstAnn(Mutable) else IP.ConstAnn(Accs)
                             | _ -> IP.ConstAnn(Mutable))
                     ) args_annl in
                     let fl = c,new_annl in
                     let new_fvs = List.map (fun c ->
                       match c with
                         | IP.IConst(i,_) -> c 
                         | _ -> IP.Var(("Anon_"^(fresh_trailer()),Unprimed),no_pos) 
                     ) args in
                     let fv = c,new_fvs in
          IP.Bag([IP.Var(x,pos)],pos),[fl],[fv])
  | _ ->  IP.Bag([],no_pos),[],[]

let rec infer_mem_from_formula (f: IF.formula) (prog: I.prog_decl) (mexp:IP.exp): 
  IF.formula * (IP.formula list) * ((ident * (IP.ann list)) list) * ((ident * (IP.exp list)) list) = 
  match f with
  | IF.Base ({
      IF.formula_base_heap = h;
      IF.formula_base_pure = p;
      IF.formula_base_vperm = vp;
      IF.formula_base_flow = fl;
      IF.formula_base_and = a;
      IF.formula_base_pos = pos;}) -> 
    let new_exp, fieldl, fieldv = infer_mem_from_heap h prog in
    let new_p = IP.BForm(((IP.mkEq mexp new_exp pos),None),None) in
    let and_p = IP.And(p,new_p,pos) in
    IF.Base {
      IF.formula_base_heap = h;
      IF.formula_base_pure = and_p;
      IF.formula_base_vperm = vp;
      IF.formula_base_flow = fl;
      IF.formula_base_and = a;
      IF.formula_base_pos = pos; }, [p], fieldl, fieldv
  | IF.Exists ({
      IF.formula_exists_qvars = qvars;
      IF.formula_exists_heap = h;
      IF.formula_exists_pure = p;
      IF.formula_exists_vperm = vp;
      IF.formula_exists_flow = fl;
      IF.formula_exists_and = a;
      IF.formula_exists_pos = pos;}) -> 
    let new_exp, fieldl, fieldv = infer_mem_from_heap h prog in
    let new_p = IP.BForm(((IP.mkEq mexp new_exp pos),None),None) in
    let and_p = IP.And(p,new_p,pos) in
    IF.Exists {
      IF.formula_exists_qvars = qvars;
      IF.formula_exists_heap = h;
      IF.formula_exists_pure = and_p;
      IF.formula_exists_vperm = vp;
      IF.formula_exists_flow = fl;
      IF.formula_exists_and = a;
      IF.formula_exists_pos = pos; }, [p], fieldl, fieldv
  | IF.Or ({IF.formula_or_f1 = f1;
            IF.formula_or_f2 = f2;
           IF.formula_or_pos = pos;}) ->  
      let new_f1,p1,fl1,fv1 = (infer_mem_from_formula f1 prog mexp) in
      let new_f2,p2,fl2,fv2 = (infer_mem_from_formula f2 prog mexp) in
      IF.Or
      {IF.formula_or_f1 = new_f1;
       IF.formula_or_f2 = new_f2;
       IF.formula_or_pos = pos;
      },p1@p2,fl1@fl2,fv1@fv2

let rec infer_mem_from_struc_formula (sf: IF.struc_formula) (prog:I.prog_decl) (mexp:IP.exp) : 
IF.struc_formula *(IP.formula list) *((ident * (IP.ann list)) list) * ((ident * (IP.exp list)) list)=
  match sf with
    (*| IF.EOr ({IF.formula_struc_or_f1 = f1;
               IF.formula_struc_or_f2 = f2;
              IF.formula_struc_or_pos = pos;}) -> 
        let new_f1,p1,fl1,fv1 = infer_mem_from_struc_formula f1 prog mexp in
        let new_f2,p2,fl2,fv2 = infer_mem_from_struc_formula f2 prog mexp in
        IF.EOr{ IF.formula_struc_or_f1 = new_f1;
        IF.formula_struc_or_f2 = new_f2;
        IF.formula_struc_or_pos = pos;},p1@p2,fl1@fl2,fv1@fv2*)
    | IF.EBase({IF.formula_struc_explicit_inst = ei;
               IF.formula_struc_implicit_inst = ii;
               IF.formula_struc_exists = e;
               IF.formula_struc_base = f;
               IF.formula_struc_is_requires = ir;
               IF.formula_struc_continuation = c;
               IF.formula_struc_pos = pos}) -> 
        let new_f,p,fl,fv = infer_mem_from_formula f prog mexp in 
              IF.EBase{IF.formula_struc_explicit_inst = ei;
               IF.formula_struc_implicit_inst = ii;
               IF.formula_struc_exists = e;
               IF.formula_struc_base = new_f;
               IF.formula_struc_is_requires = ir;
               IF.formula_struc_continuation = c;
               IF.formula_struc_pos = pos},p,fl,fv
    | IF.ECase({IF.formula_case_branches = cb;
               IF.formula_case_pos = pos}) ->
        let fs = List.map (fun (f,_) -> f) cb in
        let new_cbs_lst = List.map (fun (f,sf) -> infer_mem_from_struc_formula sf prog mexp) cb in
        let new_cbs = List.map (fun (f,_,_,_) -> f) new_cbs_lst in
        let ps = List.map (fun (_,f,_,_) -> f) new_cbs_lst in
        let fls = List.map (fun (_,_,f,_) -> f) new_cbs_lst in
        let fvs = List.map (fun (_,_,_,f) -> f) new_cbs_lst in
        IF.ECase({IF.formula_case_branches = List.combine fs new_cbs;
                 IF.formula_case_pos = pos;}),(List.flatten ps),(List.flatten fls),(List.flatten fvs)
    | IF.EAssume a -> let f = a.IF.formula_assume_simpl in
                      let flbl = a.IF.formula_assume_lbl in
                      let entyp = a.IF.formula_assume_ensures_type in
                      let sf = a.IF.formula_assume_struc in
                      let new_f,p,fl,fv = infer_mem_from_formula f prog mexp in
                      IF.EAssume({IF.formula_assume_simpl = new_f;
                                  IF.formula_assume_lbl = flbl;
                                  IF.formula_assume_ensures_type = entyp;
                                  IF.formula_assume_struc = sf;
                                 }),p,fl,fv
    | IF.EList(ls) -> let slds = List.map (fun (sld,sf) -> sld) ls in
           let new_sfs_lst = List.map (fun (_,sf) -> infer_mem_from_struc_formula sf prog mexp) ls in
           let new_sfs = List.map (fun (f,_,_,_) -> f) new_sfs_lst in
           let ps = List.map (fun (_,f,_,_) -> f) new_sfs_lst in
           let fls = List.map (fun (_,_,f,_) -> f) new_sfs_lst in
           let fvs = List.map (fun (_,_,_,f) -> f) new_sfs_lst in
           let new_ls = List.combine slds new_sfs in
           IF.EList(new_ls),(List.flatten ps),(List.flatten fls),(List.flatten fvs)
    | IF.EInfer _ -> sf,[],[],[]

let infer_mem_specs (vdef:I.view_decl) (prog:I.prog_decl) : I.view_decl =
  let mf = vdef.I.view_mem in
  match mf with
  | Some a -> let iform,p,fl,fv = infer_mem_from_struc_formula vdef.I.view_formula prog a.IF.mem_formula_exp in
              let mgfl = List.map (fun c -> IP.mkTrue no_pos) fl in
              let new_mf = {a with IF.mem_formula_field_layout = fl;
                           IF.mem_formula_field_values = fv;
                           IF.mem_formula_guards = mgfl;} in
              {vdef with I.view_formula = iform;
              I.view_mem = Some(new_mf);}
  | None -> vdef
