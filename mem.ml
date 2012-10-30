(* asankhs:  Created on 03-Sep-2012 for Memory Specifications *)
(* Uses Field Annotations (Immutable) and Bag Constraints (Mona), run with --mem --field-ann -tp om *)

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

let mk_mem_perm_formula (mem_exp: CP.exp) (isexact: bool) (fl: (ident * (CF.ann list)) list) (g: CP.formula list): CF.mem_perm_formula = 
	{ CF.mem_formula_exp = mem_exp;
	  CF.mem_formula_exact = isexact;
	  CF.mem_formula_field_layout = fl;
	  CF.mem_formula_guards = g;}

let rec intersect_list_ann_no_inter (ann_lst_l: CF.ann list) (ann_lst_r: CF.ann list): CF.ann list =
  match (ann_lst_l, ann_lst_r) with
    | ([], []) -> []
    | (ann_l :: tl, ann_r :: tr ) ->
      begin
	match ann_l, ann_r with 
	  | CF.ConstAnn(Mutable), CF.ConstAnn(Accs)
  	  | CF.ConstAnn(Imm), CF.ConstAnn(Accs) 
  	  | CF.ConstAnn(Lend), CF.ConstAnn(Accs)
	  | CF.ConstAnn(Lend), CF.ConstAnn(Lend) -> ann_l :: (intersect_list_ann_no_inter tl tr)	
  	  | CF.ConstAnn(Accs), CF.ConstAnn(Mutable)
  	  | CF.ConstAnn(Accs), CF.ConstAnn(Imm)
	  | CF.ConstAnn(Accs), CF.ConstAnn(Lend) 
  	  | CF.ConstAnn(Accs), CF.ConstAnn(Accs)-> ann_r :: (intersect_list_ann_no_inter tl tr)
  	  | _ , _ -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Spec field layouts may interfere";}

      end
    | (_, _) -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Spec should have same number of fields in layout";}

let rec intersect_list_ann (ann_lst_l: CF.ann list) (ann_lst_r: CF.ann list): CF.ann list =
  match (ann_lst_l, ann_lst_r) with
    | ([], []) -> []
    | (ann_l :: tl, ann_r :: tr ) ->
      begin
	match ann_r with 
	  | CF.ConstAnn(Mutable) -> ann_r :: (intersect_list_ann tl tr)		   
	  | CF.ConstAnn(Imm)     -> if (CF.isMutable ann_l) then ann_l :: (intersect_list_ann tl tr)
	  			 else ann_r :: (intersect_list_ann tl tr)
	  | CF.ConstAnn(Lend)    -> if (CF.isAccs ann_l) then ann_r :: (intersect_list_ann tl tr)
	  			 else ann_l :: (intersect_list_ann tl tr)
	  | CF.TempAnn _
	  | CF.ConstAnn(Accs)    -> ann_l :: (intersect_list_ann tl tr)
	  | CF.PolyAnn(v)        -> ann_l :: (intersect_list_ann tl tr) (* TODO(ann): check if var ann is replaced or not *)
      end
    | (_, _) -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Spec should have same number of fields in layout";}

let mem_guards_checking (fl1 : CP.formula) (fl2: CP.formula list) pos =
	let flag = List.exists (fun x -> let r,_,_  = TP.imply fl1 x "mem_guard_imply" false None in r) fl2 in
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
	let r,_,_  = TP.imply x relevant_slice "mem_guard_imply_reverse" false None in r) fl1 in
	if flag then ()   
	else 
	Err.report_error { Err.error_loc = pos;
	Err.error_text = "[mem.ml] : Memory Spec Guards fail during reverse implication checking";}	
		    
let rec fl_subtyping (fl1 : (ident * (CF.ann list)) list) (fl2: (ident * (CF.ann list)) list) pos =
	match fl1 with
	| [] -> ()
	| x::xs -> let matched_fields = List.filter (fun c -> if (String.compare (fst c) (fst x)) == 0 then true else false) fl2
		    (*in let _ = List.map
		    (fun c -> let _ = print_string (String.concat "," (List.map string_of_imm (snd c))) in c) fl2*)
		    in (*let _ = List.map
		    (fun c -> let _ = print_string (String.concat "," (List.map string_of_imm (snd c))) in c) fl2
		    in*) let tmp = (List.exists (fun c -> let b,_,_ = (Imm.subtype_ann_list [] (snd x) (snd c)) in 
		    (*let _ = 
		    print_string ("Ann Lists: "^ (*(string_of_bool b) ^*)(String.concat "," (List.map string_of_imm (snd c)))^" :> "^
		    		(String.concat "," (List.map string_of_imm (snd x)))^ "\n")
		    in*)
		    b) matched_fields)
		    in (*let _ = print_string ((string_of_bool tmp)^"\n") 
		    in*)  let _ = if (tmp || List.length matched_fields == 0) then () else 
			Err.report_error { Err.error_loc = pos;
			Err.error_text = "[mem.ml] : Memory Spec field layout doesn't respect annotation subtyping";}
		    in fl_subtyping fl2 xs pos

let rec fl_intersect_no_inter (fl1 : (ident * (CF.ann list)) list) (fl2: (ident * (CF.ann list)) list) : (ident * (CF.ann list)) list =
	match fl2 with
	| [] -> fl1
	| x::xs -> let _ = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then (fst c), intersect_list_ann_no_inter (snd c) (snd x) 
				else c) fl1 in fl_intersect_no_inter fl1 xs
				
let rec fl_intersect (fl1 : (ident * (CF.ann list)) list) (fl2: (ident * (CF.ann list)) list) : (ident * (CF.ann list)) list =
	match fl2 with
	| [] -> fl1
	| x::xs -> let _ = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then (fst c), intersect_list_ann (snd c) (snd x) 
				else c) fl1 in fl_intersect fl1 xs				
				
let rec fl_diff (fl1 : (ident * (CF.ann list)) list) (fl2: (ident * (CF.ann list)) list) : (ident * (CF.ann list)) list =
	match fl2 with
	| [] -> fl1
	| x::xs -> let _ = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then (fst c),Imm.replace_list_ann (snd c) (snd x) 
				else c) fl1 in fl_diff fl1 xs

let get_field_name (fl : (ident * (CF.ann list)) list) : ident = 
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
		CF.mem_formula_guards = remove_dups f1.CF.mem_formula_guards@f2.CF.mem_formula_guards;}
		(*remove_dups f1.CF.mem_formula_field_layout@f2.CF.mem_formula_field_layout;}*)

let mem_intersect (f1:CF.mem_perm_formula) (f2:CF.mem_perm_formula) : CF.mem_perm_formula =
	let pos = CP.pos_of_exp f1.CF.mem_formula_exp in
		{CF.mem_formula_exp = CP.BagIntersect(f1.CF.mem_formula_exp::[f2.CF.mem_formula_exp],pos);
		CF.mem_formula_exact = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact then true else false;
		CF.mem_formula_field_layout = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact 
					then (fl_intersect_no_inter f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout)
					else (fl_intersect f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout);
		CF.mem_formula_guards = remove_dups f1.CF.mem_formula_guards@f2.CF.mem_formula_guards;}
		
let mem_diff (f1:CF.mem_perm_formula) (f2:CF.mem_perm_formula) : CF.mem_perm_formula =
	let pos = CP.pos_of_exp f1.CF.mem_formula_exp in
		{CF.mem_formula_exp = CP.BagDiff(f1.CF.mem_formula_exp,f2.CF.mem_formula_exp,pos);
		CF.mem_formula_exact = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact then true else false;
		CF.mem_formula_field_layout = (fl_diff f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout);
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
	| CF.DataNode ({ CF.h_formula_data_node = dn;
			 CF.h_formula_data_name = name;
			 CF.h_formula_data_param_imm = fl;
			 CF.h_formula_data_pos = pos;}) -> 
			 (mk_mem_perm_formula (CP.Bag([CP.Var(dn,no_pos)],pos)) true [(name, fl)] []), []
	| CF.ViewNode ({ CF.h_formula_view_node = vn;
			 CF.h_formula_view_name = name;
			 CF.h_formula_view_arguments = argl;
			 CF.h_formula_view_pos = pos;}) -> 
			 	(*let new_var = CP.Var(CP.SpecVar((BagT (Named name)),"Anon"^(fresh_trailer()),Unprimed),pos) in 
			 	mk_mem_perm_formula (CP.Bag([new_var],pos)) false []*)
			 	let vdef = C.look_up_view_def_raw vl name in
			 	let mpf = vdef.C.view_mem in
			 	(match mpf with
				| Some mpf -> 
				 	let mexp = mpf.CF.mem_formula_exp in
				 	let gforms = mpf.CF.mem_formula_guards in
				 	(*let _ = print_string("Free Var in Mem Spec :" ^ 
				 	(String.concat "," (List.map string_of_spec_var (CP.afv mexp))) ^"\n") in
				 	let _ = print_string("Arg List :" ^ 
				 	(String.concat "," (List.map string_of_spec_var argl)) ^"\n") in*)
				 	let sbst_self = (*mexp in*)
		 	CP.e_apply_subs (List.combine [Cpure.SpecVar ((Named vdef.C.view_data_name), self, Unprimed)] [vn]) mexp in
				 	let new_mem_exp = CP.e_apply_subs (List.combine vdef.C.view_vars argl) sbst_self in
				 	(*let _ = print_string("Bag Exp :" ^ (string_of_formula_exp new_mem_exp) ^"\n") in*)
			 	        (*mk_mem_perm_formula new_mem_exp mpf.CF.mem_formula_exact mpf.CF.mem_formula_field_layout*)
			 	        (mk_mem_perm_formula new_mem_exp mpf.CF.mem_formula_exact [] gforms), []
			 	| None -> (mk_mem_perm_formula (CP.Bag([],no_pos)) false [] []),[] )
  	| CF.Hole _ | CF.HEmp | CF.HFalse | CF.HTrue -> (mk_mem_perm_formula (CP.Bag([],no_pos)) false [] []),[]

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
		  let _ = fl_subtyping mpform.CF.mem_formula_field_layout me.CF.mem_formula_field_layout pos in
		  let _ = if (CF.is_empty_heap f) then ()
		  	  else mem_guards_checking (MCP.pure_of_mix p) me.CF.mem_formula_guards pos in 
		  let f = if me.CF.mem_formula_exact 
		  	  then let f2 = CP.BForm((CP.BagSub(mfe2,mfe1,pos),None),None)
		  		in let _ = fl_subtyping me.CF.mem_formula_field_layout mpform.CF.mem_formula_field_layout pos in
		  		let _ =  if (CF.is_empty_heap f) then ()
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
		    let _ = fl_subtyping mpform.CF.mem_formula_field_layout me.CF.mem_formula_field_layout pos in
      		    let _ = if (CF.is_empty_heap f) then ()
		    	    else mem_guards_checking (MCP.pure_of_mix p) me.CF.mem_formula_guards pos in 
		    let f = if me.CF.mem_formula_exact 
		            then let f2 = CP.BForm((CP.BagSub(mfe2,mfe1,pos),None),None)
		    		 in let _ = fl_subtyping me.CF.mem_formula_field_layout mpform.CF.mem_formula_field_layout pos in
		    		 let _ = if (CF.is_empty_heap f) then ()
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
					      (mk_mem_perm_formula (CP.Bag([],no_pos)) false [] []),mix_true,[]
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
	let _ = fl_subtyping ante_mem.CF.mem_formula_field_layout conseq_mem.CF.mem_formula_field_layout pos in
	let pure_formulas = MCP.merge_mems ante_mem_pure conseq_mem_pure true in
	MCP.memo_pure_push_exists (ante_qvars@conseq_qvars) (MCP.merge_mems (MCP.mix_of_pure subset_formula) pure_formulas true)
	       	    
let get_data_fields (ddn : (ident * ((I.typed_ident * loc * bool) list)) list)  (name : ident) : ((I.typed_ident * loc * bool) list) = 
	try (snd (List.find (fun c -> (*let _ = print_string(" DD: "^(fst c)^ "N: "^name) in  *)
	if (String.compare (fst c) name) == 0 then true else false) ddn))
	with | _ -> Err.report_error {
			Err.error_loc = no_pos;
			Err.error_text = "[mem.ml] : Memory Region Field Layout not found in Data Decls";}
	
let rec get_data_decl_names (ddf : I.data_decl list) : (ident * ((I.typed_ident * loc * bool) list)) list = 
	match ddf with
	| x::xs -> (x.I.data_name,x.I.data_fields)::(get_data_decl_names xs)
	| [] -> []

let check_mem_formula_data_names (ddf : I.data_decl list) (fl : (ident * (IF.ann list))) : bool = 
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
            CF.formula_base_type = t; 
            CF.formula_base_and = ol; 
            CF.formula_base_flow = fl;
            CF.formula_base_label = lbl;
            CF.formula_base_pos = pos}) -> CF.mkBase_w_lbl (conv_h_formula_conj_to_star h) p t fl ol pos lbl
| CF.Exists ({CF.formula_exists_qvars = qvars;
	      CF.formula_exists_heap = h;
              CF.formula_exists_pure = p;
              CF.formula_exists_type = t; 
              CF.formula_exists_and = ol; 
              CF.formula_exists_flow = fl;
              CF.formula_exists_label = lbl;
              CF.formula_exists_pos = pos}) -> CF.mkExists_w_lbl qvars (conv_h_formula_conj_to_star h) p t fl ol pos lbl

let rec contains_conj (f:CF.h_formula) : bool = 
(*let _ = print_string ("Checking Conj = "^ (string_of_h_formula f) ^ "\n") in *)
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
              
let rec split_heap (h:CF.h_formula) : (CF.h_formula * CF.h_formula) = 
	(*let _ = print_string ("Splitting Heap H = "^ (string_of_h_formula h) ^ "\n") in *)
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
		    (*let _ = print_string ("H1 = "^ (string_of_h_formula h1)^ "\nH2 = "^ (string_of_h_formula h2) ^ "\n")
		    in*) (h1,h2)
	| CF.Star({CF.h_formula_star_h1 = h1;
		   CF.h_formula_star_h2 = h2;
		   CF.h_formula_star_pos = pos}) ->
		   if contains_conj h1 then
		   (*let _ = print_string ("H1 = "^ (string_of_h_formula h1)^ "\nH2 = "^ (string_of_h_formula h2) ^ "\n") in*)
		   let left_h_split = split_heap h1
		   in (fst left_h_split),(CF.mkStarH (snd left_h_split) h2 pos 27)
		   else if contains_conj h2 then
		   let right_h_split = split_heap h2
		   in (CF.mkStarH (fst right_h_split) h1 pos 28), (snd right_h_split)
		   else (h,CF.HEmp)
	| _ -> (h, CF.HEmp)

let rec remove_phases (h: IF.h_formula): IF.h_formula = 
	(*let _ = print_string ("Removing Phase from H = "^ (Iprinter.string_of_h_formula h) ^ "\n") in *)
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
	(*let _ = print_string ("Before Phase Removal H = "^ (Iprinter.string_of_h_formula h) ^ "\n") in*)
	let res = remove_phases h in	
	(*let _ = print_string ("After Phase Removal H = "^ (Iprinter.string_of_h_formula res) ^ "\n") in*) res 
	(* Push star inside A * (B /\ C) == (A * B) /\ (A * C) *) 
	(*let helper h = match h with 
	| IF.Conj({IF.h_formula_conj_h1 = h1;
		   IF.h_formula_conj_h2 = h2;
		   IF.h_formula_conj_pos = pos}) ->
	| IF.Star{IF.h_formula_star_h1 = h1;
		   IF.h_formula_star_h2 = h2;
		   IF.h_formula_star_pos = pos}) ->
	| _ -> h*)
	
let rec is_compatible_field_layout (ann_lst_l: CF.ann list) (ann_lst_r: CF.ann list): bool =	
match (ann_lst_l, ann_lst_r) with
    | ([], []) -> true
    | (ann_l :: tl, ann_r :: tr ) ->
      begin
	match ann_l, ann_r with 
	  | CF.ConstAnn(Mutable), CF.ConstAnn(Accs)
  	  | CF.ConstAnn(Imm), CF.ConstAnn(Accs) 
  	  | CF.ConstAnn(Lend), CF.ConstAnn(Accs)
	  | CF.ConstAnn(Lend), CF.ConstAnn(Lend) -> true && (is_compatible_field_layout tl tr)	
  	  | CF.ConstAnn(Accs), CF.ConstAnn(Mutable)
  	  | CF.ConstAnn(Accs), CF.ConstAnn(Imm)
	  | CF.ConstAnn(Accs), CF.ConstAnn(Lend) 
  	  | CF.ConstAnn(Accs), CF.ConstAnn(Accs)-> true && (is_compatible_field_layout tl tr)
  	  | _ , _ -> false

      end
    | (_, _) ->	false

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
		in List.exists (fun c -> (is_compatible_field_layout (snd f1) (snd c))) matched_fields) fl1
	in List.for_all (fun c -> c) t
	else false		

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
| _ -> true


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
 
let rec transform_to_tmp_ann (ann_lst: CF.ann list) : CF.ann list =
  match ann_lst with
    | [] -> []
    | ann_l::tl ->
      begin
	match ann_l with 
	  | CF.ConstAnn(ann)  -> CF.TempAnn(CF.ConstAnn(ann)) :: (transform_to_tmp_ann tl)
	  | _ -> ann_l :: (transform_to_tmp_ann tl)
      end

let rec join_ann (ann1: CF.ann list) (ann2: CF.ann list) (param1: CP.spec_var list) (param2: CP.spec_var list):
 bool * (CF.ann list) * (CP.spec_var list) (* * CP.formula*) =
 (*let tf = CP.mkTrue no_pos in*)
  match ann1, ann2,param1,param2 with
    | [], [],[],[] -> (true,[],[](*,tf*))
    | (CF.ConstAnn(Accs))::t1, a::t2, p::pt1, pa::pt2 
    | a::t1, (CF.ConstAnn(Accs))::t2, pa::pt1, p::pt2 -> let compatible, new_ann, new_param(*, new_p*) = join_ann t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, a::new_ann, pa::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | _ -> (false,[],[](*,tf*))
    
let rec join_ann_conj (ann1: CF.ann list) (ann2: CF.ann list) (param1: CP.spec_var list) (param2: CP.spec_var list):
 bool * (CF.ann list) * (CP.spec_var list) (* * CP.formula*) =
 (*let tf = CP.mkTrue no_pos in*)
  match ann1, ann2,param1,param2 with
    | [], [],[],[] -> (true,[],[](*,tf*))
    | (CF.ConstAnn(Accs))::t1, a::t2, p::pt1, pa::pt2 
    | a::t1, (CF.ConstAnn(Accs))::t2, pa::pt1, p::pt2 -> let compatible, new_ann, new_param(*, new_p*) = join_ann_conj t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, a::new_ann, pa::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | a1::t1, a2::t2, p::pt1, pa::pt2 -> let compatible, new_ann, new_param(*, new_p*) = join_ann_conj t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, a1::new_ann, p::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | _ -> (false,[],[](*,tf*))
    
let rec join_ann_conjstar (ann1: CF.ann list) (ann2: CF.ann list) (param1: CP.spec_var list) (param2: CP.spec_var list):
 bool * (CF.ann list) * (CP.spec_var list) (* * CP.formula*) =
 (*let tf = CP.mkTrue no_pos in*)
  match ann1, ann2,param1,param2 with
    | [], [],[],[] -> (true,[],[](*,tf*))
    | (CF.ConstAnn(Accs))::t1, a::t2, p::pt1, pa::pt2 
    | a::t1, (CF.ConstAnn(Accs))::t2, pa::pt1, p::pt2 -> 
    				let compatible, new_ann, new_param(*, new_p*) = join_ann_conjstar t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, a::new_ann, pa::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | (CF.ConstAnn(Lend))::t1, (CF.ConstAnn(Lend))::t2, p1::pt1, p2::pt2  -> 
    				let compatible, new_ann, new_param(*, new_p*) = join_ann_conjstar t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (true && compatible, (CF.ConstAnn(Lend))::new_ann, p1::new_param(*, (CP.mkAnd p new_p no_pos)*))
    | _ -> (false,[],[](*,tf*))
    

let rec join_ann_conjconj (ann1: CF.ann list) (ann2: CF.ann list) (param1: CP.spec_var list) (param2: CP.spec_var list):
 bool * (CF.ann list) * (CP.spec_var list) (* * CP.formula*) =
 (*let tf = CP.mkTrue no_pos in*)
  match ann1, ann2,param1,param2 with
    | [], [],[],[] -> (true,[],[](*,tf*))
    | CF.ConstAnn(ha1)::t1, CF.ConstAnn(ha2)::t2, p1::pt1, p2::pt2 -> 
    			let compatible, new_ann, new_param(*, new_p*) = join_ann_conjconj t1 t2 pt1 pt2  in
    				  (*let p = CP.mkEqVar *)
				  (ha1==ha2 && compatible, CF.ConstAnn(ha1)::new_ann, p1::new_param(*, (CP.mkAnd p new_p no_pos)*))
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
	 let aset_sv = Context.get_aset aset v1 in
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
     
let rec compact_nodes_op (h1: CF.h_formula) (h2: CF.h_formula) (aset:CP.spec_var list list) func 
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
		                  let new_h2 = CF.mkStarH h32 h42 pos2 10 in
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
		          | _ -> (h1, h2,(CP.mkTrue no_pos)) in
		      	res_h1, res_h2,res_p
	          | CF.Star {CF.h_formula_star_h1 = h11;
		                 CF.h_formula_star_h2 = h12;
		                 CF.h_formula_star_pos = pos1 } ->
	              let new_h2 = CF.mkStarH h12 h2 pos1 11 in
	              let h31, h32, p3 = compact_nodes_op h11 new_h2 aset func  in
                      let new_h2,new_p2 = compact_nodes_with_same_name_in_h_formula h32 aset in 
	              h31, new_h2,(CP.mkAnd p3 new_p2 pos1)
	          | CF.Conj {CF.h_formula_conj_h1 = h11;
				CF.h_formula_conj_h2 = h12;
			        CF.h_formula_conj_pos = pos1} ->
	              let new_h2 = CF.mkConjH h12 h2 pos1 in
	              let h31, h32, p3 = compact_nodes_op h11 new_h2 aset func in
                      let new_h2,new_p2 = compact_nodes_with_same_name_in_h_formula h32 aset in 
	              h31, new_h2,(CP.mkAnd p3 new_p2 pos1)
	          | CF.ConjStar {CF.h_formula_conjstar_h1 = h11;
				CF.h_formula_conjstar_h2 = h12;
			        CF.h_formula_conjstar_pos = pos1} ->
	              let new_h2 = CF.mkConjStarH h12 h2 pos1 in
	              let h31, h32, p3 = compact_nodes_op h11 new_h2 aset func in
                      let new_h2,new_p2 = compact_nodes_with_same_name_in_h_formula h32 aset in 
	              h31, new_h2,(CP.mkAnd p3 new_p2 pos1)
	          | CF.ConjConj {CF.h_formula_conjconj_h1 = h11;
				CF.h_formula_conjconj_h2 = h12;
			        CF.h_formula_conjconj_pos = pos1} ->
	              let new_h2 = CF.mkConjConjH h12 h2 pos1 in
	              let h31, h32, p3 = compact_nodes_op h11 new_h2 aset func in
                      let new_h2,new_p2 = compact_nodes_with_same_name_in_h_formula h32 aset in 
	              h31, new_h2,(CP.mkAnd p3 new_p2 pos1)	              	              	              
		  | _ -> h1,h2,(CP.mkTrue no_pos))  
                   
and compact_nodes_with_same_name_in_h_formula (f: CF.h_formula) (aset: CP.spec_var list list) : CF.h_formula * CP.formula = 
  (*let _ = print_string("Compacting :"^ (string_of_h_formula f)^ "\n") in*)
  if not (!Globals.allow_field_ann) then f,(CP.mkTrue no_pos) else
    match f with
      | CF.Star {CF.h_formula_star_h1 = h1;
                 CF.h_formula_star_h2 = h2;
                 CF.h_formula_star_pos = pos } ->             
	let h1,h2,_ = compact_nodes_op h1 h2 aset join_ann in
	let res = CF.mkStarH h1 h2 pos 12 in
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
	        let h1,h2,_ = compact_nodes_op h1 h2 aset join_ann_conjconj in
		let res = CF.mkConjConjH h1 h2 pos in
		res,(CP.mkTrue no_pos)		 	        
      | CF.Phase h ->  let h1_h,h1_p = compact_nodes_with_same_name_in_h_formula h.CF.h_formula_phase_rd aset in
      		let h2_h,h2_p = compact_nodes_with_same_name_in_h_formula h.CF.h_formula_phase_rw aset in
      		let and_p = CP.mkAnd h1_p h2_p h.CF.h_formula_phase_pos in
      		CF.Phase {h with CF.h_formula_phase_rd = h1_h;
 	      CF.h_formula_phase_rw = h2_h;},and_p
      | _ -> f,(CP.mkTrue no_pos)

let rec compact_nodes_with_same_name_in_formula (cf: CF.formula): CF.formula =
  match cf with
    | CF.Base f   -> let new_h,new_p = 
    	compact_nodes_with_same_name_in_h_formula f.CF.formula_base_heap (Context.comp_aliases f.CF.formula_base_pure)
    	in 
    	(*let new_mcp = MCP.merge_mems f.CF.formula_base_pure (MCP.mix_of_pure new_p) true in*)
    	CF.Base { f with
        CF.formula_base_heap = new_h;       
	(*CF.formula_base_pure = new_mcp;*)}
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
    	compact_nodes_with_same_name_in_h_formula h (Context.comp_aliases mp)
    	in
    	(*let p_list = List.filter (fun c -> match c with
    	| CP.BForm((CP.Eq (e1,e2,_),None),None) -> (match e1,e2 with
    				| CP.Var(s1,_) , CP.Var(s2,_) -> not ((List.mem s1 qevars) || (List.mem s2 qevars))
    				| _ -> false)
    	| _ -> false) (CP.list_of_conjs new_p) in
    	let new_p = CP.conj_of_list p_list f.CF.formula_exists_pos in*)
 	(*let new_mcp = MCP.merge_mems mp (MCP.mix_of_pure new_p) true in*)
	(*let new_mcp = MCP.memo_pure_push_exists f.CF.formula_exists_qvars new_mcp in*)
    	CF.Exists { f with
    	CF.formula_exists_qvars = qevars;
        CF.formula_exists_heap = new_h;
        (*CF.formula_exists_pure = new_mcp;*)}

let rec compact_nodes_with_same_name_in_struc (f: CF.struc_formula): CF.struc_formula = (* f *)
  if not (!Globals.allow_field_ann ) then f
  else
    match f with
      | CF.EOr sf            -> CF.EOr { sf with 
          CF.formula_struc_or_f1 = compact_nodes_with_same_name_in_struc sf.CF.formula_struc_or_f1;
          CF.formula_struc_or_f2 = compact_nodes_with_same_name_in_struc  sf.CF.formula_struc_or_f2;} 
      | CF.EList sf          -> CF.EList  (map_l_snd compact_nodes_with_same_name_in_struc sf) 
      | CF.ECase sf          -> CF.ECase {sf with CF.formula_case_branches = map_l_snd compact_nodes_with_same_name_in_struc sf.CF.formula_case_branches;} 
      | CF.EBase sf          -> CF.EBase {sf with
          CF.formula_struc_base =  compact_nodes_with_same_name_in_formula sf.CF.formula_struc_base;
          CF.formula_struc_continuation = map_opt compact_nodes_with_same_name_in_struc sf.CF.formula_struc_continuation; }
      | CF.EAssume (x, f, y)-> CF.EAssume (x,(compact_nodes_with_same_name_in_formula f),y)
      | CF.EInfer sf         -> CF.EInfer {sf with CF.formula_inf_continuation = compact_nodes_with_same_name_in_struc sf.CF.formula_inf_continuation}
        
let rec is_lend_h_formula (f : CF.h_formula) : bool =  match f with
  | CF.DataNode (h1) -> 
        if (CF.isLend h1.CF.h_formula_data_imm) then
          (* let _ = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n")  in *) true
        else
        if !Globals.allow_field_ann && (Imm.isExistsLendList h1.CF.h_formula_data_param_imm) then true
        else
          false
  | CF.ViewNode (h1) ->
        if (CF.isLend h1.CF.h_formula_view_imm) then
          (* let _ = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n") in *) true
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
	CF.h_formula_star_pos = pos}) -> (is_lend_h_formula h1) or (is_lend_h_formula h2)
  | CF.Hole _ -> false
  | _ -> false
  
        
let rec is_lend (f : CF.formula) : bool =  
(match f with
  | CF.Base(bf) -> is_lend_h_formula bf.CF.formula_base_heap
  | CF.Exists(ef) -> is_lend_h_formula ef.CF.formula_exists_heap
  | CF.Or({CF.formula_or_f1 = f1;
    CF.formula_or_f2 = f2;
    CF.formula_or_pos = pos}) ->
        (is_lend f1) or (is_lend f2))
        
let subtype_sv_ann_gen (impl_vars: CP.spec_var list) (l: CP.spec_var) (r: CP.spec_var) 
: bool * (CP.formula option) * (CP.formula option) =
	let l = CP.Var(l,no_pos) in
	let r = CP.Var(r,no_pos) in
	let c = CP.BForm ((CP.SubAnn(l,r,no_pos),None), None) in
        (* implicit instantiation of @v made stronger into an equality *)
        (* two examples in ann1.slk fail otherwise; unsound when we have *)
        (* multiple implicit being instantiated ; use explicit if needed *)
        let lhs = CP.BForm ((CP.Eq(l,r,no_pos),None), None) in
        (* let lhs = c in *)
        begin
          match r with
            | CP.Var(v,_) -> 
                if CP.mem v impl_vars then (true,Some lhs,None)
                else (true,None,Some c)
            | _ -> (true,None,Some c)
        end

let rec subtype_sv_ann_gen_list (impl_vars: CP.spec_var list) (ls: CP.spec_var list) (rs: CP.spec_var list)
: bool * (CP.formula option) * (CP.formula option) = 
match ls, rs with
| [], [] -> (true,None,None)
| l::ls, r::rs -> let f, lhs, rhs = (subtype_sv_ann_gen impl_vars l r) in
		  let fs, lhsls, rhsrs = (subtype_sv_ann_gen_list impl_vars ls rs) in
		  (f && fs, (Imm.mkAndOpt lhs lhsls) , (Imm.mkAndOpt rhs rhsrs))
| _,_ -> (false,None,None)(* shouldn't get here *)
