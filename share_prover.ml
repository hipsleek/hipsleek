
module type SV =
sig 
  type t 
  val eq: t->t->bool
  val string_of : t->string
  val rename : t -> string -> t
  val get_name : t -> string
  val fresh_var : t -> t
  val var_of : string -> t
end;;

module type TREE_CONST = 
    sig
      type t_sh
	  val top : t_sh
	  val bot : t_sh
	  val mkNode : t_sh -> t_sh -> t_sh
	  val empty : t_sh -> bool
	  val full : t_sh -> bool
	  val depth_0 : t_sh -> bool
	  val rleft : t_sh -> t_sh
	  val rright : t_sh -> t_sh
	  val avg : t_sh -> t_sh -> t_sh
    end;;
 
module type SAT_SLV = functor (Sv : SV) ->
sig 
	type t_var = Sv.t
	type nz_cons = t_var list list 
	type p_var = 
		| PVar of t_var 
		| C_top
	type eq_syst = (t_var*t_var*p_var) list
	val call_sat:  nz_cons -> eq_syst -> bool
	val call_imply: t_var list -> nz_cons -> eq_syst -> t_var list -> nz_cons -> eq_syst -> (t_var*bool) list -> (t_var*t_var) list-> bool
end;;
 
module type DFRAC_SOLVER =
  sig
	 type eq_syst
	 val is_sat : eq_syst -> bool
	 val imply : eq_syst -> eq_syst -> bool
	 val e_elim : eq_syst -> eq_syst
  end;;
  
module Dfrac_s_solver = functor (Ts : TREE_CONST) -> functor (SV : SV) -> functor (Ss1 : SAT_SLV) ->
	struct
		module Ss= Ss1(SV)
		type t_var = SV.t
		type const_sh = Ts.t_sh
		type frac_perm = 
			| Vperm of t_var 
			| Cperm of const_sh
		type eq = frac_perm * frac_perm * frac_perm

		type eq_syst = t_var list * t_var list  * eq list (*exist vars, eq list*)
		
		(*todo consistency checks, reduce to the simple form with one constant*)
		exception Unsat_exception
		exception Unsat_conseq of bool
		
		let report_error s = failwith s 
		
		(*aux functions*)
		let fv f = match f with 
			| Vperm v -> [v]
			| _ -> []
		
		let mem_eq eq x l = List.exists (eq x) l
		let rec remove_dups_eq eq n =  match n with [] -> [] | q::qs -> if (mem_eq eq q qs) then remove_dups_eq eq qs else q::(remove_dups_eq eq qs)	
		
		let eq_fv (e1,e2,e3) = (fv e1)@(fv e2)@(fv e3)
		let eq_sys_fv l = remove_dups_eq SV.eq (List.concat (List.map eq_fv l))
			
		(*let fold_2 l = List.fold_left (fun (a1,a2) (c1,c2)-> a1@c1, a2@c2) ([],[]) l	
		let fold_3 l = List.fold_left (fun (a1,a2,a3) (c1,c2,c3)-> a1@c1, a2@c2, a3@c3) ([],[],[]) l*)
		let fold_1_map f l = List.fold_left (fun a c -> (f c)@a) [] l 
		let fold_2_map f l = List.fold_left (fun (a1,a2) c-> 
			let c1,c2 = f c in
			a1@c1, a2@c2) ([],[]) l
		let fold_3_map f l = List.fold_left (fun (a1,a2,a3) c-> 
			let c1,c2,c3 = f c in
			a1@c1, a2@c2, a3@c3) ([],[],[]) l
		let fold_12_map f i l= List.fold_left (fun (a1,a2) c-> 
			let c1,c2 = f c a2 in
			a1@c1, c2) i l
		let fold_13_map f i l= List.fold_left (fun (a1,a2,a3) c-> 
			let c1,c2,c3 = f c a3 in
			a1@c1, a2@c2,c3) i l
		
		let subst_ex (f,t) v = if (SV.eq v f) then t else v
		let subst_ex_l (f,t) l = List.map (subst_ex (f,t)) l
			
		let rename_ex (ev, nz, l_eq) = 
			let sub = List.map (fun v-> (v, SV.fresh_var v)) ev in
			let ren_var v = try snd (List.find (fun (v1,_)-> SV.eq v v1) sub) with | Not_found -> v in
			let ren_v v = match v with | Vperm v-> Vperm (ren_var v) | _ -> v in
			let ren_eq (v1,v2,v3)= ren_v v1, ren_v v2, ren_v v3 in
			snd (List.split sub), List.map ren_var nz, List.map ren_eq l_eq
			
		let rec check_const_incons vc_l = match vc_l with
				| [] -> ()
				| (v,c)::t -> 
					try 
						let _,c2 = List.find (fun (v2,_) -> SV.eq v v2) t in
						if c2 <> c then raise Unsat_exception
						else check_const_incons t
					with Not_found ->check_const_incons t 
				
		let check_eq_incons ve_l = 
			List.iter (fun (e1,e2,e3)-> if Ss.C_top=e3 & SV.eq e1 e2 then raise Unsat_exception else ()) ve_l
				
				
		let triv_subst vc vv eq_l = 
			let sub_v_c (f,t) v = match v with | Cperm _ -> v | Vperm v1-> if (SV.eq f v1) then Cperm t else v in
			let sub_eq_c c (e1,e2,e3) = sub_v_c c e1,sub_v_c c e2,sub_v_c c e3 in		
			let vc  = List.map (fun (v,c) -> v,if c then Ts.top else Ts.bot) vc in
			let eq_l = List.fold_left (fun eq_l c-> List.map (sub_eq_c c) eq_l) eq_l vc in
			
			let sub_v_v (f,t) v = match v with | Cperm _ -> v | Vperm v1-> if (SV.eq f v1) then Vperm t else v in
			let sub_eq_v c (e1,e2,e3) = sub_v_v c e1, sub_v_v c e2, sub_v_v c e3 in			
			List.fold_left (fun eq_l c-> List.map (sub_eq_v c) eq_l) eq_l vv 			
				
		(*decomposition functions*)
		let gen_left_name n = n^"(" 
		let gen_left_var v = SV.rename v (gen_left_name (SV.get_name v))
		
		let gen_right_name n = n^")" 
		let gen_right_var v = SV.rename v (gen_right_name (SV.get_name v))
		
		let eq_depth_0 ef = match ef with
			| Cperm d, Vperm _, Vperm _
			| Vperm _, Cperm d, Vperm _
			| Vperm _, Vperm _, Cperm d -> Ts.depth_0 d
			| _ -> report_error "unexpected equation structure"
			
		let decompose_fp (f:frac_perm) = match f with 
			| Vperm vp -> 
				[vp], Vperm (gen_left_var vp), Vperm (gen_left_var vp)
						(*	let n = SV.get_name vp in 
							let vl = SV.rename vp (gen_left_name n) in
							let vr = SV.rename vp (gen_right_name n) in*)
			| Cperm cp ->
				[],Cperm (Ts.rleft cp),Cperm (Ts.rright cp)
				
		let decomp_no_lim (e1,e2,e3) = 
			let s1, l1,r1 = decompose_fp e1 in
			let s2, l2,r2 = decompose_fp e2 in
			let s3, l3,r3 = decompose_fp e3 in
			(s1@s2@s3), (l1,l2,l3), (r1,r2,r3)
			
		let rec decompose_eq eq = 
			if eq_depth_0 eq then [],[eq]
			else 
				let lvs, l_eq, r_eq = decomp_no_lim eq in
				let lstl,eqsl = decompose_eq l_eq in
				let lstr,eqsr = decompose_eq r_eq in
				lstl@lstr@lvs , eqsl@eqsr		
		
		let decompose_sys leqs = 
			(*if a variable is decomposed in some eq, it will need to be decomposed in all eqs*)
			let rec one_pass b l_vs acc leqs = match leqs with
				| [] -> (b,l_vs,acc)
				| h::t -> 
					if List.exists (fun v1-> mem_eq SV.eq v1 l_vs) (eq_fv h) then 
						let lv,leq,req = decomp_no_lim h in
						one_pass true (l_vs@lv) acc (leq::req::t)
					else
					 one_pass b l_vs (h::acc) t in
					 
			let rec fix_helper l_vs l_eqs = 
				let b,l_vs,l_eqs = one_pass false l_vs [] l_eqs in
				if b then fix_helper l_vs l_eqs 
				else (l_vs,l_eqs) in
				
			let l_decomp_vs, leqs = fold_2_map decompose_eq leqs in
			let l_decomp_vs, leqs = fix_helper l_decomp_vs leqs in
			let l_decomp_vs = remove_dups_eq SV.eq l_decomp_vs in
			l_decomp_vs, leqs
		
		let all_decomps l_decs v = (*returns only the leafs of the decompositions*)
			let rec fp v = if mem_eq SV.eq v l_decs then (fp (gen_left_var v))@(fp (gen_right_var v)) else [v] in
			fp v
		
		let all_decomps_l l_decs vl = fold_1_map (all_decomps l_decs) vl 
		
		let longest_subst lst a v = 
			(*find if there exists some var that needs decomposition in lst to get to v*)
			(*finds the largest substring*)
			let nv = SV.get_name v in
			let ac = List.fold_left (fun ac v-> 
				let nvv = SV.get_name v in
				let lnvv = String.length nvv in
				if BatString.starts_with nv nvv then 
					match ac with 
						| None -> Some (lnvv,v)
						| Some (nacv, acv) -> 
							if lnvv > nacv then  Some (lnvv,v)
							else ac
				else ac) None lst in
			match ac with 
				| Some (_,v)-> v::a
				| None -> a
				
		let meet_decompositions (avl,ael) (cvl,cel) int_vs=  
			let expand vl el exp_l = 
				let expand_one (vl,el) v = 
					let expand_one_one_acc (nvl,eq_acc) eq = 
						if mem_eq SV.eq v (eq_fv eq) then 
							let lv,leq,req = decomp_no_lim eq in
							lv@nvl, leq::req::eq_acc 
						else (nvl,eq::eq_acc) in
					let nvl, el = List.fold_left expand_one_one_acc ([],[]) el in
					remove_dups_eq SV.eq (vl@nvl), el in			
				List.fold_left expand_one (vl,el) exp_l in
			
			let rec fix (avl,ael) (cvl,cel) a_int_vs (*decomposed in ante*) c_int_vs (*decomposed in conseq*) =
				let c_exp = remove_dups_eq SV.eq (List.fold_left (longest_subst cvl) [] a_int_vs) in (*what needs decomposing in conseq*)
				let a_exp = remove_dups_eq SV.eq (List.fold_left (longest_subst avl) [] c_int_vs) in (*what needs decomposing in ante*)
				if a_exp=[] && c_exp=[] then avl,ael,cvl,cel
				else 
					let avl,ael = expand avl ael a_exp in
					let cvl,cel = expand cvl cel c_exp in
					fix (avl,ael) (cvl,cel) (all_decomps_l avl a_int_vs) (all_decomps_l cvl c_int_vs) in
			fix (avl,ael) (cvl,cel) (all_decomps_l avl int_vs) (all_decomps_l cvl int_vs)
			
		
		(*simplification  functions, reductions to v*v=v*)
		let compute_nz_cons nzv decomp_vs vc_l ve_l  = 
			let nz_cons = List.map (all_decomps decomp_vs) nzv in 
			let nz_cons = List.fold_left (fun nz (f,t) -> List.map (subst_ex_l (f,t)) nz) nz_cons ve_l in
			let nz_cons	= List.fold_left (fun nz (v,c) -> 
				if c then List.filter (fun d-> not (mem_eq SV.eq v d)) nz
				else List.map (fun d-> List.filter (fun v1-> not (SV.eq v v1)) d) nz) nz_cons vc_l in
			if (List.exists (fun c-> c=[]) nz_cons) then raise Unsat_exception
			else nz_cons 
		
		let simpl_vars r1 r2 r3 = 
			if SV.eq r1 r2 then [(r1,false);(r3,false)],[]
			else if SV.eq r1 r3 then [(r2,false)],[] 
			else if SV.eq r2 r3 then [(r1,false)],[] 
			else [],[(r1,r2,Ss.PVar r3)]
		
		let c_v_solver ex_l e = match e with
			| Cperm d, Vperm v1, Vperm v2 
			| Vperm v1, Cperm d, Vperm v2 -> 
				if Ts.empty d then 
					if mem_eq SV.eq v2 ex_l then ([],[(v2,v1)],[])
					else ([],[(v1,v2)],[])
				else ([(v1,false);(v2,true)],[],[])
				(*if Ts.full d then report_error "incomplete decomposition"*)
			| Vperm v1, Vperm v2, Cperm d ->
				if Ts.empty d then ([(v1,false);(v2,false)],[],[])
				else ([],[],[(v1,v2,Ss.C_top)])
				(*if Ts.full d then else report_error "incomplete decomposition"*)
			| Cperm d1, Cperm d2, Vperm v -> 
				if (Ts.full d1)&&(Ts.full d2) then raise Unsat_exception else ([(v,Ts.full d1 || Ts.full d2)],[],[])
			| Cperm d1, Vperm v, Cperm d2 
			| Vperm v, Cperm d1, Cperm d2 -> (match Ts.full d2,Ts.full d1 with 
				| true, true -> ([(v,false)],[],[])
				| true, false -> ([(v,true)],[],[])
				| false, false -> ([(v,false)],[],[])
				| false, true -> raise Unsat_exception)
			| Vperm v1, Vperm v2, Vperm v3 -> let r1,r2 = simpl_vars v1 v2 v3 in (r1,[],r2)
			| Cperm d1, Cperm d2, Cperm d3 -> 
				let fd1 = Ts.full d1 in
				let fd2 = Ts.full d2 in
				let fd3 = Ts.full d3 in
				if (not (fd1 && fd2) && fd3=(fd1||fd2)) then ([],[],[]) else raise Unsat_exception
					
			
		let rec appl_substs exvl consts subs eqs =
			let ex_subst v1 v2 = if mem_eq SV.eq v2 exvl then (v2,v1) else (v1,v2) in
			let subst_ex_eq p (v1,v2,v3) = 
				let r1 = subst_ex p v1 in
				let r2 = subst_ex p v2 in
				match v3 with 
				| Ss.C_top -> if SV.eq r1 r2 then raise Unsat_exception else ([],[(r1,r2,Ss.C_top)])
				| Ss.PVar v -> simpl_vars r1 r2 (subst_ex p v) in
					
			let solve_2 (v,c) (v1,v2,v3s) = 
				let s1 = SV.eq v1 v in
				let s2 = SV.eq v2 v in
				match v3s with 
					| Ss.C_top -> (match s1,s2 with
						| true, true -> raise Unsat_exception
						| false,false ->([],[],[(v1,v2,v3s)])
						| true, false ->([v2,not c],[],[])
						| false, true ->([v1,not c],[],[]))
					| Ss.PVar v3->
						let s3 = SV.eq v3 v in
						(match s1,s2,s3,c with 
							| true,true,_,true -> raise Unsat_exception 
							| true,true,true, false -> ([],[],[])
							| true,true,false, false -> ([v3,c],[],[])
							| false,false,true,true-> ([],[],[(v1,v2,Ss.C_top)]) 
							| false,false,true,false-> ([(v1,c);(v2,c);(v3,c)],[],[])
							| false,false, false, _ -> ([],[],[(v1,v2,v3s)])
							| true, false, true, _ -> ([(v2,false)],[],[])
							| false, true, true, _ -> ([(v1,false)],[],[])
							| true, false, false, true -> ([(v2,not c);(v3,c)],[],[])
							| false, true, false, true -> ([(v1,not c);(v3,c)],[],[])
							| true, false, false, false -> ([],[ex_subst v2 v3],[])
							| false, true, false, false -> ([],[ex_subst v1 v3],[])) in
			if consts=[] & subs=[] then (consts,subs,eqs)
			else
				let consts = List.fold_left (fun c_l (f,t)-> List.map (fun (v,c)-> subst_ex (f,t) v, c) c_l) consts subs in
				let nc_l, eqs = fold_12_map (fun (f,t) eql-> fold_2_map (subst_ex_eq (f,t)) eql) ([],eqs) subs in
				let nc_l2, ns_l, eqs = fold_13_map (fun (v,c) eql -> fold_3_map (solve_2 (v,c)) eql) ([],[],eqs) consts in
				let cr,sr,er = appl_substs exvl (nc_l@nc_l2) ns_l eqs in
				consts@cr, subs@sr, er
			
				
		let solve_trivial_eq_l ex_l l = 	
			(*first pass: reduces eq syst to v=c , v=v, v+v=(v|1) *)
			let l_c, l_s, l_e = fold_3_map (c_v_solver ex_l) l in
			(*second pass, apply subst until fixpoint is reached*)
			let l_c, l_s, l_e = appl_substs ex_l l_c l_s l_e in
			check_const_incons l_c;
			check_eq_incons l_e;
			l_c, l_s, l_e
			
								
		let to_formula_sat nzv eqs  = 
		   (*decomposes the vars, returns the simplified syst to v*v=(v|1) and non-zero constraints*)
			let dec_vars, l_eqs = decompose_sys eqs in
			let const_vars, subst_vars,l_eqs = solve_trivial_eq_l [] l_eqs in
			let nz_cons = compute_nz_cons nzv dec_vars const_vars subst_vars in
			(nz_cons,l_eqs)
			
		let is_sat ((_,nzv,eqs) : eq_syst): bool = 
		    if eqs=[] then true 
			else
				try
				let (nz,l_eqs) = to_formula_sat nzv eqs in
				Ss.call_sat nz l_eqs
				with Unsat_exception -> false
			
		let to_formula_imply a_sys c_sys:bool =
			(*decomposes the vars, returns the list of decomposed vars, var subst, var instantiations, simplified syst to v*v=(v|1) for both ante and conseq *)
			
			(*rename existentials to avoid clashes*)
			let a_ev,a_nzv,a_eq = rename_ex a_sys in
			let c_ev,c_nzv,c_eq = rename_ex c_sys in
			
			(*intersection variables*)
			let int_fv = 
				let afv = eq_sys_fv a_eq in
				let cfv = eq_sys_fv c_eq in
				List.filter (fun v-> mem_eq SV.eq v cfv) afv in
				
			(*decompose each system*)
			let c_d_vs,c_l_eqs = try decompose_sys c_eq with | Unsat_exception -> raise (Unsat_conseq (not (is_sat ([],a_nzv,a_eq)))) in
			let a_d_vs,a_l_eqs = decompose_sys a_eq in
			
			(*further decompose both until each var is at the same level of decomposition*)
			let a_dec_vars, a_l_eqs, c_dec_vars, c_l_eqs = meet_decompositions (a_d_vs,a_l_eqs) (c_d_vs,c_l_eqs) int_fv in
			
			(*decomp the existentials as well*)
			let a_ev = List.fold_left (fun a c-> a@(all_decomps a_dec_vars c)) [] a_ev in
			let c_ev = List.fold_left (fun a c-> a@(all_decomps c_dec_vars c)) [] c_ev in
			
			(*simplify the antecedent*)
			let a_const_vars, a_subst_vars, a_l_eqs = solve_trivial_eq_l a_ev a_l_eqs in
			let a_nz_cons = compute_nz_cons a_nzv a_dec_vars a_const_vars a_subst_vars in
			
			(*apply the substitutions from the antecedent to the conseq*)
			let c_l_eqs = triv_subst a_const_vars a_subst_vars c_l_eqs in
			
			(*simplify the conseq*)
			try
				let c_const_vars, c_subst_vars, c_l_eqs = solve_trivial_eq_l c_ev c_l_eqs in
				let c_nz_cons = compute_nz_cons c_nzv c_dec_vars c_const_vars c_subst_vars in
				Ss.call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars
			with | Unsat_exception -> not (Ss.call_sat a_nz_cons a_l_eqs)
			
				
		let imply  (a_sys : eq_syst) (c_sys : eq_syst) : bool = 
			let _,_,c_eq = c_sys in
			if c_eq=[] then true
			else
				try
					to_formula_imply a_sys c_sys 
				with 
				 | Unsat_exception -> true
				 | Unsat_conseq b -> b
							
		
		let e_elim (eqs : eq_syst) : eq_syst = eqs
		
end;;

	

(*concrete modules*)	

module Ts = Tree_shares.Ts
module Sv = 
  struct
	type t=string
	let cnt = ref 1
	let eq v1 v2 = (String.compare v1 v2) = 0
    let string_of v1 = v1
	let rename _ s = s
    let get_name v = v
	let var_of v = v
    let fresh_var _ = cnt:=!cnt+1; "__ts_fv_"^(string_of_int !cnt)    
end

module Ss_triv = functor (Sv:SV) ->
  struct
	type t_var = Sv.t
	type nz_cons = t_var list list 
	type p_var = (*include Gen.EQ_TYPE with type t=v*)
		| PVar of t_var 
		| C_top
	type eq_syst = (t_var*t_var*p_var) list
	let call_sat _ _ = true 
	let call_imply _ _ _ _ _ _ _ _  = false 
end;;


module Ss_Z3 = functor (Sv:SV) ->
  struct
	type t_var = Sv.t
	type nz_cons = t_var list list 
	type p_var = (*include Gen.EQ_TYPE with type t=v*)
		| PVar of t_var 
		| C_top
	type eq_syst = (t_var*t_var*p_var) list
		
		(**********Z3 interface **********)
		
		(** Create a boolean variable using the given name. *)
		let mk_bool_var ctx name = Z3.mk_const ctx (Z3.mk_string_symbol ctx name) (Z3.mk_bool_sort ctx)
		let mk_sv_bool_var ctx sv  =  mk_bool_var ctx (Sv.get_name sv)
		
		(** Create a logical context.  Enable model construction. Also enable tracing to stderr. *)
		let mk_context ctx = 
			let ctx = Z3.mk_context_x (Array.append [|("MODEL", "false")|] ctx) in
			Z3.trace_to_stderr ctx;(* You may comment out this line to disable tracing: *)
			ctx
		
		(** Check if  ctx is sat. if sat, then could get the model.*)
		let check ctx =(match Z3.check ctx with
			| Z3.L_FALSE -> false
			| Z3.L_UNDEF ->  print_string "unknown\n"; failwith "unknown sat"
			| Z3.L_TRUE -> true )
		
		let add_eqs ctx non_zeros eqs = 
			List.iter (fun l-> Z3.assert_cnstr ctx (Z3.mk_or ctx (Array.of_list (List.map (mk_sv_bool_var ctx) l))) ) non_zeros;
			List.iter (fun (v1,v2,v3)-> 
				let bv1 = mk_sv_bool_var ctx v1 in
				let bv2 = mk_sv_bool_var ctx v2 in
				let xor12 = Z3.mk_xor ctx bv1 bv2 in
				Z3.assert_cnstr ctx (Z3.mk_not ctx (Z3.mk_and ctx [|bv1;bv2|]));
				match v3 with 
					| PVar v3-> Z3.assert_cnstr ctx (Z3.mk_eq ctx xor12 (mk_sv_bool_var ctx v3))
					| C_top  -> Z3.assert_cnstr ctx xor12
				) eqs
		
	let call_sat non_zeros eqs = 
		let ctx = mk_context [||] in
		add_eqs ctx non_zeros eqs;
		let r = check ctx in
		Z3.del_context ctx;
		r
	
	let call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars  = 
		let ctx = mk_context [||] in
		add_eqs ctx a_nz_cons a_l_eqs;
			let tbl = Hashtbl.create 20 in
			let bool_sort = Z3.mk_bool_sort ctx in
			let _ = List.fold_left (fun c v-> Hashtbl.add tbl (Sv.get_name v) (Z3.mk_bound ctx c bool_sort); c+1) 1 c_ev in
			let mk_sv_bool_var_ex v = 
				let nm = Sv.get_name v in
				try
					Hashtbl.find tbl nm
				with Not_found -> mk_bool_var ctx nm in	
				
		let conseq = 
			let f_ccv = List.fold_left (fun a (v,c)-> 
					let z3v = mk_sv_bool_var_ex v in
					let z3v = if c then z3v else Z3.mk_not ctx z3v  in
					Z3.mk_and ctx [| a ; z3v|])
				(Z3.mk_true ctx) c_const_vars in
			let f_sv = List.fold_left (fun a (v1,v2)-> 
					let z3v1 = mk_sv_bool_var_ex v1 in
					let z3v2 = mk_sv_bool_var_ex v2 in
					let z3eq = Z3.mk_eq ctx z3v1 z3v2 in
					Z3.mk_and ctx [|a; z3eq|])
				f_ccv c_subst_vars in
			let f_nz = List.fold_left (fun a l -> 
					let nz_arr = Array.of_list (List.map mk_sv_bool_var_ex l) in
					let and_arr = Array.append [|a|] nz_arr in
					Z3.mk_and ctx and_arr
				) f_sv c_nz_cons in
			let f_eqs = List.fold_left (fun a (v1,v2,v3)-> 
				let z3v1 = mk_sv_bool_var_ex v1 in
				let z3v2 = mk_sv_bool_var_ex v2 in
				let xor12 = Z3.mk_xor ctx z3v1 z3v2 in
				let f1 = Z3.mk_not ctx (Z3.mk_and ctx [|z3v1;z3v2|]) in
				let a  = Z3.mk_and ctx [|a;f1|] in
				match v3 with
					| PVar v3 -> Z3.mk_and ctx [| a;  Z3.mk_eq ctx xor12 (mk_sv_bool_var_ex v3) |]
					| C_top -> Z3.mk_and ctx [| a;  xor12 |]
			) f_nz c_l_eqs in
				
			let l = List.length c_ev in
			let types = Array.init l (fun _ -> bool_sort) in
			let names = Array.init l (Z3.mk_int_symbol ctx) in
			Z3.mk_forall ctx 0 [||] types names f_eqs in
			
		Z3.assert_cnstr ctx (Z3.mk_not ctx conseq);	
		let r = Z3.check ctx in
		Z3.del_context ctx;
		match r with
				| Z3.L_FALSE ->	true			
				| Z3.L_UNDEF ->	print_string "unknown\n"; false 
				| Z3.L_TRUE  ->	false 
end;;


module Solver = Dfrac_s_solver(Ts)(Sv)(Ss_Z3)

module Eqs = 
	struct 
	type var = Sv.t
	type const = Ts.stree
	type pcvar = Solver.frac_perm
	type eq = Solver.eq
	type eq_syst = Solver.eq_syst
	let mkVar = Sv.var_of
	let mkEq v1 v2 v3 = (v1,v2,v3)
	let mkEqS l1 l2 l3 = (l1,l2,l3)
	let mkcFull = Ts.top
	let mkcEmpty = Ts.bot
	let mkcNode = Ts.mkNode 
	let mkpcCnst c = Solver.Cperm c
	let mkpcVar v = Solver.Vperm v
end
    
type cmd = 
	| Sat of Eqs.eq_syst
	| Imply of Eqs.eq_syst * Eqs.eq_syst