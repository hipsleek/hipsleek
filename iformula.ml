(*
  Created 19-Feb-2006

  Input formulae
*)

open Globals
module P = Ipure

  
type struc_formula = ext_formula list

and ext_formula = 
	| ECase of ext_case_formula
	| EBase of ext_base_formula


and ext_case_formula =
	{
		formula_case_branches : (P.formula * struc_formula ) list;
		formula_case_pos : loc 		
	}

and ext_base_formula =
	{
		 formula_ext_explicit_inst : (ident * primed) list;
		 formula_ext_implicit_inst : (ident * primed) list;
		 formula_ext_base : formula;
		 formula_ext_continuation : struc_formula;
		 formula_ext_pos : loc
	}

and formula =
  | Base of formula_base
  | Exists of formula_exists
  | Or of formula_or

and formula_base = { formula_base_heap : h_formula;
					 formula_base_pure : P.formula;
					 formula_base_pos : loc }

and formula_exists = { formula_exists_qvars : (ident * primed) list;
					   formula_exists_heap : h_formula;
					   formula_exists_pure : P.formula;
					   formula_exists_pos : loc }

and formula_or = { formula_or_f1 : formula;
				   formula_or_f2 : formula;
				   formula_or_pos : loc }

and h_formula = (* heap formula *)
  | Star of h_formula_star
  | HeapNode of h_formula_heap
  | HeapNode2 of h_formula_heap2
	  (* Don't distinguish between view and data node for now, as that requires look up *)
	  (*  | ArrayNode of ((ident * primed) * ident * P.exp list * loc) *)
	  (* pointer * base type * list of dimensions *)
  | HTrue 
  | HFalse
	  
and h_formula_star = { h_formula_star_h1 : h_formula;
					   h_formula_star_h2 : h_formula;
					   h_formula_star_pos : loc }

and h_formula_heap = { h_formula_heap_node : (ident * primed);
					   h_formula_heap_name : ident;
					   h_formula_heap_full : bool;
					   h_formula_heap_with_inv : bool;
					   h_formula_heap_arguments : P.exp list;
					   h_formula_heap_pseudo_data : bool;
					   h_formula_heap_pos : loc }

and h_formula_heap2 = { h_formula_heap2_node : (ident * primed);
						h_formula_heap2_name : ident;
						h_formula_heap2_full : bool;
						h_formula_heap2_with_inv : bool;
						h_formula_heap2_arguments : (ident * P.exp) list;
						h_formula_heap2_pseudo_data : bool;
						h_formula_heap2_pos : loc }

(* constructors *)

let rec formula_of_heap h pos = mkBase h (P.mkTrue pos) pos

and formula_of_pure p pos = mkBase HTrue p pos

and isConstFalse f0 = match f0 with
  | Base f -> begin
	  let h, p = f.formula_base_heap, f.formula_base_pure in
		match h with
		  | HFalse -> true
		  | _ -> match p with
			  | P.BForm (P.BConst (false, _)) -> true
			  | _ -> false
	end
  | _ -> false

and isConstTrue f0 = match f0 with
  | Base f -> begin
	  let h, p = f.formula_base_heap, f.formula_base_pure in
		match h with
		  | HTrue -> begin
			  match p with
				| P.BForm (P.BConst (true, _)) -> true
				| _ -> false
			end
		  | _ -> false
	end
  | _ -> false

and isEConstFalse f0 = match f0 with
  | [EBase b] -> isConstFalse b.formula_ext_base
  | _ -> false

and isEConstTrue f0 = match f0 with
 	| [EBase b] -> isConstTrue b.formula_ext_base
  | _ -> false

and mkTrue pos = Base { formula_base_heap = HTrue;
						formula_base_pure = P.mkTrue pos;
						formula_base_pos = pos }

and mkFalse pos = Base { formula_base_heap = HFalse;
						 formula_base_pure = P.mkFalse pos;
						 formula_base_pos = pos }


and mkETrue pos = [EBase {
		 formula_ext_explicit_inst = [];
		 formula_ext_implicit_inst = [];
		 formula_ext_base = mkTrue pos;
		 formula_ext_continuation = [];
		 formula_ext_pos = pos	}]

and mkEFalse pos =[EBase {
		 formula_ext_explicit_inst = [];
		 formula_ext_implicit_inst = [];
		 formula_ext_base = mkFalse pos;
		 formula_ext_continuation = [];
		 formula_ext_pos = pos	}]
																				
and mkEOr f1 f2 pos = 
	if isEConstTrue f1 || isEConstTrue f2 then
	mkETrue pos
  else if isEConstFalse f1 then f2
  else if isEConstFalse f2 then f1
  else List.rev_append f1 f2

and mkOr f1 f2 pos =
  if isConstTrue f1 || isConstTrue f2 then
	mkTrue pos
  else if isConstFalse f1 then f2
  else if isConstFalse f2 then f1
  else Or { formula_or_f1 = f1;
			formula_or_f2 = f2;
			formula_or_pos = pos }

and mkBase (h : h_formula) (p : P.formula) pos = match h with
  | HFalse -> mkFalse pos
  | _ -> 
	  if P.isConstFalse p then 
		mkFalse pos 
	  else 
		Base { formula_base_heap = h;
			   formula_base_pure = p;
			   formula_base_pos = pos }

and mkExists (qvars : (ident * primed) list) (h : h_formula) (p : P.formula) pos = match h with
  | HFalse -> mkFalse pos
  | _ ->
	  if P.isConstFalse p then
		mkFalse pos
	  else
		Exists { formula_exists_qvars = qvars;
				 formula_exists_heap = h;
				 formula_exists_pure = p;
				 formula_exists_pos = pos }

and mkStar f1 f2 pos = match f1 with
  | HFalse -> HFalse
  | HTrue -> f2
  | _ -> match f2 with
	  | HFalse -> HFalse
	  | HTrue -> f1
	  | _ -> Star { h_formula_star_h1 = f1;
					h_formula_star_h2 = f2;
					h_formula_star_pos = pos }


and h_arg_fv (f:h_formula):(ident*primed) list = 
	let rec helper (f:h_formula):((ident*primed) list) *( (ident*primed) list) =	match f with   
  | Star b -> 
		let r11,r12 =  helper b.h_formula_star_h1 in
		let r21,r22 =  helper b.h_formula_star_h2 in
		((r11@r21),(r12@r22))
  | HeapNode {h_formula_heap_node = name ; 
							h_formula_heap_arguments = b}->
		((List.map (fun c->match c with
			|Ipure.Var d -> (fst d) 
			| _ -> 	Error.report_error	{Error.error_loc = no_pos; Error.error_text = "exp float out malfunction"} ) b) ,[name])
  | HeapNode2 { h_formula_heap2_node = name ;
								h_formula_heap2_arguments = b}->		
		((List.map (fun c->match (snd c) with
			|Ipure.Var d -> (fst d) 
			| _ -> 	Error.report_error	{Error.error_loc = no_pos; Error.error_text = "exp float out malfunction"} ) b) ,[name])
  | HTrue -> ([],[]) 
  | HFalse -> ([],[]) in
	let r1,r2 = helper f in
	Util.remove_dups (Util.difference r1 r2)
	
and h_fv (f:h_formula):(ident*primed) list = match f with   
  | Star b ->  Util.remove_dups ((h_fv b.h_formula_star_h1)@(h_fv b.h_formula_star_h2))
  | HeapNode {h_formula_heap_node = name ; 
							h_formula_heap_arguments = b} -> Util.remove_dups (name:: (List.concat (List.map Ipure.afv b)))
  | HeapNode2 { h_formula_heap2_node = name ;
								h_formula_heap2_arguments = b}-> Util.remove_dups (name:: (List.concat (List.map (fun c-> (Ipure.afv (snd c))) b) ))
  | HTrue -> [] 
  | HFalse -> [] 


and fv (f:formula):(ident*primed) list = match f with
	| Base b-> h_arg_fv b.formula_base_heap
	| Exists b-> h_arg_fv b.formula_exists_heap
	| Or b-> Util.remove_dups ((fv b.formula_or_f1)@(fv b.formula_or_f2))

and pos_of_struc_formula f0  = match (List.hd f0) with 
	| ECase b -> b.formula_case_pos
	| EBase b -> b.formula_ext_pos

and pos_of_formula f0 = match f0 with
  | Base f -> f.formula_base_pos
  | Or f -> f.formula_or_pos
  | Exists f -> f.formula_exists_pos

and split_quantifiers (f : formula) : ( (ident * primed) list * formula) = match f with
  | Exists ({formula_exists_qvars = qvars; 
			 formula_exists_heap =  h; 
			 formula_exists_pure = p; 
			 formula_exists_pos = pos}) -> 
      (qvars, mkBase h p pos)
  | Base _ -> ([], f)
  | _ -> failwith ("split_quantifiers: invalid argument")



(*var substitution*)

and subst sst (f : formula) = match sst with
  | s :: rest -> subst rest (apply_one s f)
  | [] -> f 
      
and subst_var (fr, t) (o : (ident*primed)) = if (Ipure.eq_var fr o) then t else o
and subst_var_list ft (o : (ident*primed)) = let r = List.filter (fun (c1,c2)-> (Ipure.eq_var c1 o) ) ft in
	if (List.length r)==0 then o else snd (List.hd r)

and apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
      Or ({formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos})
  | Base ({formula_base_heap = h;
					 formula_base_pure = p;
					 formula_base_pos = pos }) -> 
      Base ({formula_base_heap = h_apply_one s h; 
			 formula_base_pure = Ipure.apply_one s p; 
			 formula_base_pos = pos})
  | Exists ({formula_exists_qvars = qsv; 
			 formula_exists_heap = qh; 
			 formula_exists_pure = qp; 
			 formula_exists_pos = pos}) -> 
	  if List.mem (fst fr) (List.map fst qsv) then f 
	  else Exists ({formula_exists_qvars = qsv; 
					formula_exists_heap =  h_apply_one s qh; 
					formula_exists_pure = Ipure.apply_one s qp; 
					formula_exists_pos = pos})		

and h_apply_one ((fr, t) as s : ((ident*primed) * (ident*primed))) (f : h_formula) = match f with
  | Star ({h_formula_star_h1 = f1; 
		   h_formula_star_h2 = f2; 
		   h_formula_star_pos = pos}) -> 
      Star ({h_formula_star_h1 = h_apply_one s f1; 
			 h_formula_star_h2 = h_apply_one s f2; 
			 h_formula_star_pos = pos})
  | HeapNode ({h_formula_heap_node = x; 
			   h_formula_heap_name = c; 
			   h_formula_heap_full = full; 
			   h_formula_heap_with_inv = winv;
			   h_formula_heap_arguments = args;
			   h_formula_heap_pseudo_data = ps_data;
			   h_formula_heap_pos = pos}) -> 
      HeapNode ({h_formula_heap_node = subst_var s x; 
				 h_formula_heap_name = c; 
				 h_formula_heap_full = full;
				 h_formula_heap_with_inv = winv;
				 h_formula_heap_arguments = List.map (Ipure.e_apply_one s) args;
				 h_formula_heap_pseudo_data = ps_data;
				 h_formula_heap_pos = pos})
  | HeapNode2 ({
		 				h_formula_heap2_node = x;
						h_formula_heap2_name = c;
						h_formula_heap2_full = full;
						h_formula_heap2_with_inv = winv;
						h_formula_heap2_arguments = args;
						h_formula_heap2_pseudo_data = ps_data;
						h_formula_heap2_pos= pos}) -> 
      HeapNode2 ({
				 		h_formula_heap2_node = subst_var s x;
						h_formula_heap2_name =c;
						h_formula_heap2_full =full;
						h_formula_heap2_with_inv = winv;
						h_formula_heap2_arguments = List.map (fun (c1,c2)-> (c1,(Ipure.e_apply_one s c2))) args;
						h_formula_heap2_pseudo_data =ps_data;
						h_formula_heap2_pos = pos})
  | HTrue -> f
  | HFalse -> f
	  



and rename_bound_vars (f : formula) = 
	let add_quantifiers (qvars : (ident*primed) list) (f : formula) : formula = match f with
  | Base ({formula_base_heap = h; 
		   formula_base_pure = p; 
		   formula_base_pos = pos}) -> mkExists qvars h p pos
  | Exists ({formula_exists_qvars = qvs; 
			 formula_exists_heap = h; 
			 formula_exists_pure = p; 
			 formula_exists_pos = pos}) -> 
	  let new_qvars = Util.remove_dups (qvs @ qvars) in
		mkExists new_qvars h p pos
  | _ -> failwith ("add_quantifiers: invalid argument") in		
	match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	  let rf1 = rename_bound_vars f1 in
	  let rf2 = rename_bound_vars f2 in
	  let resform = mkOr rf1 rf2 pos in
		resform
  | Base _ -> f
  | Exists _ ->
	  let qvars, base_f = split_quantifiers f in
	  let new_qvars = Ipure.fresh_vars qvars in
	  let rho = List.combine qvars new_qvars in
	  let new_base_f = subst rho base_f in
	  let resform = add_quantifiers new_qvars new_base_f in
		resform 


	
and subst_struc (sst:((ident * primed)*(ident * primed)) list) (f:struc_formula):struc_formula = 
	
	let rec helper (f:ext_formula):ext_formula = match f with
		| ECase b ->
			let r = List.map (fun (c1,c2)-> ((Ipure.subst sst c1),(subst_struc sst c2))) b.formula_case_branches in
			ECase ({formula_case_branches = r; formula_case_pos = b.formula_case_pos})
		| EBase b->
			let sb = subst sst b.formula_ext_base in
			let sc = subst_struc sst b.formula_ext_continuation in
			let se = List.map (subst_var_list sst) b.formula_ext_explicit_inst in
			let si = List.map (subst_var_list sst) b.formula_ext_implicit_inst in
			EBase ({
					formula_ext_implicit_inst = si;
					formula_ext_explicit_inst = se;
				  formula_ext_base = sb;
					formula_ext_continuation = sc;
					formula_ext_pos = b.formula_ext_pos	})	in	
	List.map helper f
				
								
and rename_bound_vars_struc (f:struc_formula):struc_formula =
	let rec helper (f:ext_formula):ext_formula = match f with
		| ECase b-> ECase ({b with formula_case_branches = List.map (fun (c1,c2)-> (c1,(rename_bound_vars_struc c2))) b.formula_case_branches})
		| EBase b-> 
			let sst1 = List.map (fun (c1,c2)-> ((c1,c2),((Ipure.fresh_old_name c1),c2)))b.formula_ext_explicit_inst in
			let sst2 = List.map (fun (c1,c2)-> ((c1,c2),((Ipure.fresh_old_name c1),c2)))b.formula_ext_implicit_inst in
			let sst = sst1@sst2 in
			let nb = subst sst b.formula_ext_base in
			let nc = subst_struc sst b.formula_ext_continuation in		
			let new_base_f = rename_bound_vars nb in
			let new_cont_f = rename_bound_vars_struc nc in
			EBase ({b with 
				formula_ext_explicit_inst = snd (List.split sst1);
		 		formula_ext_implicit_inst = snd (List.split sst2);
				formula_ext_base=new_base_f; formula_ext_continuation=new_cont_f})			
			in
	List.map helper f



and norm_formula (h:(ident*primed) list) (nw:bool) (f:formula):formula*((ident*primed)list)=match f with
	| Base b-> (*should i take into consideration alias sets as well??*)
		let fe_h = (h_arg_fv b.formula_base_heap) in
		let fe = Util.remove_dups (fe_h @ (Ipure.fv b.formula_base_pure)) in		
		let exvar = Util.difference fe h in
		let _ = if nw && ((List.length (Util.difference exvar fe_h)) > 0) then 	Error.report_error	{Error.error_loc = no_pos; Error.error_text = "there are free vars in the pure"} 
							else if (List.length (List.filter (fun (c1,c2)-> c2 == Primed ) exvar))>0 then   Error.report_error	{Error.error_loc = no_pos; Error.error_text = "existential vars should not be primed"}
							else true in 
		let h1 = Util.difference fe exvar in
		if (List.length exvar) == 0 then (f,h1)
			else (Exists ({
						 formula_exists_qvars = exvar;
					   formula_exists_heap = b.formula_base_heap;
					   formula_exists_pure = b.formula_base_pure;
					   formula_exists_pos = b.formula_base_pos
				}),h1) 			
	| Exists b-> 
			let fe_h = (h_arg_fv b.formula_exists_heap) in
			let fe = Util.remove_dups (fe_h @ (Ipure.fv b.formula_exists_pure)@b.formula_exists_qvars) in		
			let exvar = Util.difference fe h in
			let _ = if nw && ((List.length (Util.difference exvar fe_h)) > 0) then 	Error.report_error	{Error.error_loc = no_pos; Error.error_text = "there are free vars in the pure"} 
							else if (List.length (List.filter (fun (c1,c2)-> c2 == Primed ) exvar))>0 then   Error.report_error	{Error.error_loc = no_pos; Error.error_text = "existential vars should not be primed"}
							else true in 
			let h1 = Util.difference fe exvar in
			if (List.length exvar) == 0 then 
				(Base ({
					formula_base_heap = b.formula_exists_heap;
					formula_base_pure = b.formula_exists_pure;
					formula_base_pos = b.formula_exists_pos
					}),h1)
				else (Exists ({b with formula_exists_qvars = exvar}),h1)
	| Or  b-> 
		let f1,r1= norm_formula h nw b.formula_or_f1 in
		let f2,r2= norm_formula h nw b.formula_or_f2 in
			 (Or({formula_or_f1 = f1;
				   formula_or_f2 = f2;
				   formula_or_pos =b.formula_or_pos }), (Util.remove_dups (r1@r2)))


and float_out_exps_from_heap (f:formula ):formula = 
	
	let rec float_out_exps (f:h_formula):(h_formula * (((ident*primed)*Ipure.formula)list)) = match f with
		 | Star b-> 
				let r11,r12 = float_out_exps b.h_formula_star_h1 in
				let r21,r22 = float_out_exps b.h_formula_star_h2 in
				(Star ({h_formula_star_h1  =r11; h_formula_star_h2=r21;h_formula_star_pos = b.h_formula_star_pos}), 
				(r12@r22))
 		 | HeapNode b-> 
				let na,ls = List.split (List.map (fun c->
								match c with
									| Ipure.Var _ -> (c,[])
									| _ -> 
										let nn = (("flted_"^(fresh_trailer ())),Unprimed) in
										let nv = Ipure.Var (nn,b.h_formula_heap_pos) in
										let npf = Ipure.BForm (Ipure.Eq (nv,c,b.h_formula_heap_pos)) in																
										(nv,[(nn,npf)])) b.h_formula_heap_arguments) in
				(HeapNode ({b with h_formula_heap_arguments = na}),(List.concat ls))
  	 | HeapNode2 b ->	 
				let na,ls = List.split (List.map (fun c->
								match (snd c) with
									| Ipure.Var _ -> (c,[])
									| _ -> 
										let nn = (("flted_"^(fresh_trailer ())),Unprimed) in
										let nv = Ipure.Var (nn,b.h_formula_heap2_pos) in
										let npf = Ipure.BForm (Ipure.Eq (nv,(snd c),b.h_formula_heap2_pos)) in																
										(((fst c),nv),[(nn,npf)])) b.h_formula_heap2_arguments) in
				(HeapNode2 ({b with h_formula_heap2_arguments = na}),(List.concat ls))
  	 | HTrue -> (f,[])
     | HFalse -> (f,[]) in
	
	let rec helper (f:formula):formula =	match f with
	| Base b-> let rh,rl = float_out_exps b.formula_base_heap in
						 if (List.length rl)== 0 then f
							else 
								let r1,r2 = List.hd rl in
								let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)-> ((c1::a1),(Ipure.mkAnd a2 c2 b.formula_base_pos)) ) ([r1],r2) (List.tl rl) in
								Exists ({
								 formula_exists_qvars = r1;
							   formula_exists_heap = rh;
							   formula_exists_pure = Ipure.mkAnd r2 b.formula_base_pure b.formula_base_pos;
							   formula_exists_pos = b.formula_base_pos
								})			
	| Exists b->
			let rh,rl = float_out_exps b.formula_exists_heap in
		 	if (List.length rl)== 0 then f
							else 
								let r1,r2 = List.hd rl in
								let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)-> ((c1::a1),(Ipure.mkAnd a2 c2 b.formula_exists_pos)) ) ([r1],r2) (List.tl rl) in
							Exists ({
								 formula_exists_qvars = r1@b.formula_exists_qvars;
							   formula_exists_heap = rh;
							   formula_exists_pure = Ipure.mkAnd r2 b.formula_exists_pure b.formula_exists_pos;
							   formula_exists_pos = b.formula_exists_pos
								})	
	| Or b-> Or ({
					 formula_or_f1 = float_out_exps_from_heap b.formula_or_f1;
				   formula_or_f2 = float_out_exps_from_heap b.formula_or_f2;
				   formula_or_pos = b.formula_or_pos
		})		
	in helper f

and normalize_struc ((hp1,hp2):((ident*primed)list * (ident*primed)list)) (f0: struc_formula):struc_formula*((ident*primed) list) = 
	let helper (f0:ext_formula):ext_formula*((ident*primed) list) = match f0 with
		| ECase b->
			let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)->
									let r12 = Util.intersect (Ipure.fv c1) hp1 in
									let r21,r22 = normalize_struc (hp1,hp2) c2 in
									(((c1,r21)::a1),r12::r22::a2)
					) ([],[]) b.formula_case_branches in				
					(ECase ({
						formula_case_branches = r1;
						formula_case_pos = b.formula_case_pos
						}),(Util.remove_dups (List.concat r2)))			
		| EBase b->		
				let nh0 = b.formula_ext_explicit_inst in
				let _ = if (List.length (Util.intersect hp1 nh0))>0 then 
						(*let _ = print_string ("late:"^(List.fold_left (fun a (c1,c2)-> a^","^c1^(match c2 with Unprimed -> " "|Primed ->"' ")) "" nh0)^
																	"\t used: "^(List.fold_left (fun a (c1,c2)-> a^","^c1^(match c2 with Unprimed -> " "|Primed ->"' ")) "" hp1)^"\n") in*)
						Error.report_error {Error.error_loc = b.formula_ext_pos; Error.error_text = "the late instantiation variables collide with the used vars"}
					else true in
				let h1 = Util.remove_dups (hp1@nh0) in
				let onb = convert_anonym_to_exist b.formula_ext_base in
				let h0prm = Util.difference (fv onb) h1 in
				let h0h0prm = Util.remove_dups (nh0@h0prm) in
				let h1prm = Util.remove_dups (h1@h0prm) in
				let _ = if (List.length (List.filter (fun (c1,c2)-> c2==Primed) h0h0prm))>0 then
						Error.report_error {Error.error_loc = b.formula_ext_pos; Error.error_text = "should not have prime vars"} else true in
				let _ = if (List.length (Util.intersect(h0h0prm) hp2))>0 then 	
						Error.report_error {Error.error_loc = b.formula_ext_pos; Error.error_text = "post variables should not appear here"} else true in
				let nc,h2 = normalize_struc (h1prm,hp2) b.formula_ext_continuation in	
				let implvar = Util.difference h2 h1 in
				let nb,h3 = norm_formula (Util.remove_dups(h1@implvar)) false onb in
				
				let _ = if (List.length (Util.difference implvar (fv onb)))>0 then 
						Error.report_error {Error.error_loc = b.formula_ext_pos; Error.error_text = "malfunction: some implicit vars are heap_vars"} else true in
				(EBase ({
					formula_ext_base = nb;
					formula_ext_implicit_inst =implvar;					
					formula_ext_explicit_inst = b.formula_ext_explicit_inst;
					formula_ext_continuation = nc;
					formula_ext_pos = b.formula_ext_pos}),(Util.remove_dups (h2@h3))) in
	let l1 = List.map helper f0 in
	let ll1,ll2 = List.split l1 in
	(ll1, (Util.remove_dups (List.concat ll2)))

	
and float_out_exps_from_heap_struc (f:struc_formula):struc_formula = 
	let rec helper (f:ext_formula):ext_formula = match f with
		| ECase b -> ECase ({formula_case_branches = List.map (fun (c1,c2)-> (c1,(float_out_exps_from_heap_struc c2))) b.formula_case_branches ; formula_case_pos=b.formula_case_pos})
		| EBase b-> 	EBase ({
					formula_ext_explicit_inst = b.formula_ext_explicit_inst;
					formula_ext_implicit_inst = b.formula_ext_implicit_inst;
					formula_ext_base = float_out_exps_from_heap b.formula_ext_base;
					formula_ext_continuation = float_out_exps_from_heap_struc b.formula_ext_continuation;
					formula_ext_pos = b.formula_ext_pos			
				})in	
	List.map helper f
	
	
and formula_to_struc_formula (f:formula):struc_formula =
	let rec helper (f:formula):struc_formula = match f with
		| Base b-> [EBase ({
			 		formula_ext_explicit_inst =[];
		 			formula_ext_implicit_inst = [];
		 			formula_ext_base = f;
					formula_ext_continuation = [];
		 			formula_ext_pos = b.formula_base_pos})]
		| Exists b-> [EBase ({
			 		formula_ext_explicit_inst =[];
		 			formula_ext_implicit_inst = [];
		 			formula_ext_base = f;
					formula_ext_continuation = [];
		 			formula_ext_pos = b.formula_exists_pos})]
		| Or b->  (helper b.formula_or_f1)@(helper b.formula_or_f2) in			
	(helper f)
	
(***********************************************)
(* 17.04.2008 *)
(* add existential quantifiers for the anonymous vars - those that start with "Anon_" *)
(***********************************************)
and

	(* - added 17.04.2008 - checks if the heap formula contains anonymous    *)
	(* vars                                                                  *)
  (* as h*) (* as h*)
	(* let _ = print_string("[astsimpl.ml, line 163]: anonymous var: " ^ id  *)
	(* ^ "\n") in                                                            *)
  look_for_anonymous_h_formula (h0 : h_formula) : (ident * primed) list =
  match h0 with
  | Star { h_formula_star_h1 = h1; h_formula_star_h2 = h2 } ->
      let tmp1 = look_for_anonymous_h_formula h1 in
      let tmp2 = look_for_anonymous_h_formula h2 in List.append tmp1 tmp2
  | HeapNode { h_formula_heap_arguments = args } ->
      let tmp1 = Ipure.look_for_anonymous_exp_list args in tmp1
  | _ -> []


		
and convert_anonym_to_exist (f0 : formula) : formula =
  match f0 with
  | (* - added 17.04.2008 - in case the formula contains anonymous vars ->   *)
			(* transforms them into existential vars (transforms IF.formula_base *)
			(* to IF.formula_exists)                                             *)
    Or (({ formula_or_f1 = f1; formula_or_f2 = f2 } as f)) ->
      let tmp1 = convert_anonym_to_exist f1 in
      let tmp2 = convert_anonym_to_exist f2
      in Or { (f) with formula_or_f1 = tmp1; formula_or_f2 = tmp2; }
  | Base
      {
        formula_base_heap = h0;
        formula_base_pure = p0;
        formula_base_pos = l0
      } -> (*as f*)
      let tmp1 = look_for_anonymous_h_formula h0
      in
        if ( != ) (List.length tmp1) 0
        then
          Exists
            {
              formula_exists_heap = h0;
              formula_exists_qvars = tmp1;
              formula_exists_pure = p0;
              formula_exists_pos = l0;
            }
        else f0
  | Exists
      (({ formula_exists_heap = h0; formula_exists_qvars = q0 } as f))
      ->
      let tmp1 = look_for_anonymous_h_formula h0
      in
        if ( != ) (List.length tmp1) 0
        then
          (let rec append_no_duplicates (l1 : (ident * primed) list)
             (l2 : (ident * primed) list) : (ident * primed) list =
             match l1 with
             | h :: rest ->
                 if List.mem h l2
                 then append_no_duplicates rest l2
                 else h :: (append_no_duplicates rest l2)
             | [] -> l2
           in
             Exists
               {
                 (f)
                 with
                 formula_exists_heap = h0;
                 formula_exists_qvars = append_no_duplicates tmp1 q0;
               })
        else (* make sure that the var is not already there *) f0

