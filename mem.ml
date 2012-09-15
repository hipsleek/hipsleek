(* asankhs:  Created on 03-Sep-2012 for Memory Specifications *)
(* Uses Field Annotations (Immutable) and Bag Constraints (Mona), run with --field-ann -tp om *)

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

let mk_mem_perm_formula (mem_exp: CP.exp) (isexact: bool) (fl: (ident * (CF.ann list)) list) : CF.mem_perm_formula = 
	{ CF.mem_formula_exp = mem_exp;
	  CF.mem_formula_exact = isexact;
	  CF.mem_formula_field_layout = fl;}

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

let rec fl_subtyping (fl1 : (ident * (CF.ann list)) list) (fl2: (ident * (CF.ann list)) list) =
	match fl2 with
	| [] -> ()
	| x::xs -> let _ = List.map (fun c -> if (String.compare (fst c) (fst x)) == 0 
				then let (tmp ,_,_) = (Imm.subtype_ann_list [] (snd c) (snd x)) in
				(*let _ = print_string ("Ann lists: " ^ (String.concat "," (List.map string_of_imm (snd c)))^" "^
					(String.concat "," (List.map string_of_imm (snd x)))^ "\n") in *)
				if tmp then c else 
				 	Err.report_error { Err.error_loc = no_pos;
					Err.error_text = "[mem.ml] : Memory Spec field layout doesn't respect annotation subtyping";}
				else c) fl1 in fl_subtyping fl1 xs
			
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
		CF.mem_formula_field_layout = remove_dups f1.CF.mem_formula_field_layout@f2.CF.mem_formula_field_layout;}
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
		CF.mem_formula_field_layout = remove_dups f1.CF.mem_formula_field_layout@f2.CF.mem_formula_field_layout;}

let mem_intersect (f1:CF.mem_perm_formula) (f2:CF.mem_perm_formula) : CF.mem_perm_formula =
	let pos = CP.pos_of_exp f1.CF.mem_formula_exp in
		{CF.mem_formula_exp = CP.BagIntersect(f1.CF.mem_formula_exp::[f2.CF.mem_formula_exp],pos);
		CF.mem_formula_exact = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact then true else false;
		CF.mem_formula_field_layout = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact 
					then (fl_intersect_no_inter f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout)
					else (fl_intersect f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout);}
		
let mem_diff (f1:CF.mem_perm_formula) (f2:CF.mem_perm_formula) : CF.mem_perm_formula =
	let pos = CP.pos_of_exp f1.CF.mem_formula_exp in
		{CF.mem_formula_exp = CP.BagDiff(f1.CF.mem_formula_exp,f2.CF.mem_formula_exp,pos);
		CF.mem_formula_exact = if f1.CF.mem_formula_exact && f2.CF.mem_formula_exact then true else false;
		CF.mem_formula_field_layout = (fl_diff f1.CF.mem_formula_field_layout f2.CF.mem_formula_field_layout);}

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
			 (mk_mem_perm_formula (CP.Bag([CP.Var(dn,no_pos)],pos)) true [(name, fl)]), []
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
				 	(*let _ = print_string("Free Var in Mem Spec :" ^ 
				 	(String.concat "," (List.map string_of_spec_var (CP.afv mexp))) ^"\n") in
				 	let _ = print_string("Arg List :" ^ 
				 	(String.concat "," (List.map string_of_spec_var argl)) ^"\n") in*)
				 	let sbst_self = (*mexp in*)
		 	CP.e_apply_subs (List.combine [Cpure.SpecVar ((Named vdef.C.view_data_name), self, Unprimed)] [vn]) mexp in
				 	let new_mem_exp = CP.e_apply_subs (List.combine vdef.C.view_vars argl) sbst_self in
				 	(*let _ = print_string("Bag Exp :" ^ (string_of_formula_exp new_mem_exp) ^"\n") in*)
			 	        (*mk_mem_perm_formula new_mem_exp mpf.CF.mem_formula_exact mpf.CF.mem_formula_field_layout*)
			 	        (mk_mem_perm_formula new_mem_exp mpf.CF.mem_formula_exact []), []
			 	| None -> (mk_mem_perm_formula (CP.Bag([],no_pos)) false []),[] )
  	| CF.Hole _ | CF.HEmp | CF.HFalse | CF.HTrue -> (mk_mem_perm_formula (CP.Bag([],no_pos)) false []),[]

let rec xmem (f: CF.formula) (vl:C.view_decl list) (me: CF.mem_perm_formula): MCP.mix_formula =
	match f with
	| CF.Or ({CF.formula_or_f1 = f1;
		CF.formula_or_f2 = f2;
		CF.formula_or_pos = pos;}) -> (*MCP.mkOr_mems (xmem f1 vl me) (xmem f2 vl me) *)
						MCP.merge_mems (xmem f1 vl me) (xmem f2 vl me) true
	| CF.Base ({ CF.formula_base_heap = f;
		  CF.formula_base_pos = pos;}) -> 
		  let mpform,disjform = (xmem_heap f vl) in
         	  let mfe1 = me.CF.mem_formula_exp in
		  let mfe2 = mpform.CF.mem_formula_exp in
		  let f1 = CP.BForm((CP.BagSub(mfe1,mfe2,pos),None),None) in
		  let _ = fl_subtyping mpform.CF.mem_formula_field_layout me.CF.mem_formula_field_layout in
		  let f = if me.CF.mem_formula_exact 
		  	  then let f2 = CP.BForm((CP.BagSub(mfe2,mfe1,pos),None),None)
		  		in let _ = fl_subtyping me.CF.mem_formula_field_layout mpform.CF.mem_formula_field_layout
		  		in MCP.merge_mems (MCP.mix_of_pure f1) (MCP.mix_of_pure f2) true
		  	  else MCP.mix_of_pure f1 
		  in (List.fold_left (fun a b -> MCP.merge_mems a (MCP.mix_of_pure b) true) f disjform)
	| CF.Exists ({ CF.formula_exists_qvars = qvars;
		    CF.formula_exists_heap = f;
		    CF.formula_exists_pos = pos;}) -> 
		    let mpform,disjform = (xmem_heap f vl) in
		    let mfe1 = me.CF.mem_formula_exp in
		    let mfe2 = mpform.CF.mem_formula_exp in
		    let f1 = CP.BForm((CP.BagSub(mfe1,mfe2,pos),None),None) in
		    let _ = fl_subtyping mpform.CF.mem_formula_field_layout me.CF.mem_formula_field_layout in
		    let f = if me.CF.mem_formula_exact 
		            then let f2 = CP.BForm((CP.BagSub(mfe2,mfe1,pos),None),None)
		    		 in let _ = fl_subtyping me.CF.mem_formula_field_layout mpform.CF.mem_formula_field_layout
				 in let fe = MCP.merge_mems (MCP.mix_of_pure f1) (MCP.mix_of_pure f2) true
				 (*in MCP.memo_pure_push_exists qvars fe*)
				 in fe
		    		 else (MCP.mix_of_pure f1)
		    		      (*MCP.memo_pure_push_exists qvars (MCP.mix_of_pure f1)*)
       	    in MCP.memo_pure_push_exists qvars (List.fold_left (fun a b -> MCP.merge_mems a (MCP.mix_of_pure b) true) f disjform)

let compute_mem_spec (prog : C.prog_decl) (lhs : CF.formula) (rhs : CF.formula) (pos: loc) = 
	let formula1 = lhs in
	(*let _ = print_string("LHS :"^(string_of_formula formula1) ^"\n") in*)
	let ctx = CF.build_context (CF.true_ctx ( CF.mkTrueFlow ()) Lab2_List.unlabelled pos) formula1 pos in
	let formula = rhs in
	(*let _ = print_string("RHS :" ^(string_of_formula formula)^"\n") in*)
  	let (rs, _) = Solver.heap_entail_init prog false (CF.SuccCtx [ ctx ]) formula pos in
	if not(CF.isFailCtx rs) then ()
	else Err.report_error {Err.error_loc = pos;
	Err.error_text = "[mem.ml] : view formula does not entail supplied Memory Spec";}

let validate_mem_spec (prog : C.prog_decl) (vdef: C.view_decl) = 
	match vdef.C.view_mem with
	| Some a -> let pos = CF.pos_of_struc_formula vdef.C.view_formula in 
		    let list_of_disjuncts = fst (List.split vdef.C.view_un_struc_formula) in 
	            let list_of_calcmem = 
	            List.map (fun c -> CF.formula_of_mix_formula (xmem c prog.C.prog_view_decls a) pos) list_of_disjuncts in
	            let combined_list = List.combine list_of_disjuncts list_of_calcmem in
	            let _ = List.map (fun c-> compute_mem_spec prog (fst c) (snd c) pos) combined_list in ()
		    (*let calcmem = 
		    MCP.simpl_memo_pure_formula Solver.simpl_b_formula Solver.simpl_pure_formula calcmem (TP.simplify_a 10) in 
		    let lhs = CF.formula_of_mix_formula vdef.C.view_x_formula pos in
		    let rhs = CF.formula_of_mix_formula calcmem pos in*)	 
	| None -> ()
	
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
  			let allvs = IP.afv a.IF.mem_formula_exp in
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

