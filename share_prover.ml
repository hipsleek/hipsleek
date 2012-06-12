module type SV =
sig 
  type t
  (*type t_spec*)
  (*val conv: t-> t_spec
  val rconv: t_spec -> t*)
  val eq: t->t->bool
  val string_of : t->string
  (*val string_of_s : t_spec->string*)
  val rename : t -> string -> t
  val get_name : t -> string
  (*val get_name_s : t_spec -> string*)
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
	  (*val avg : t_sh -> t_sh -> t_sh*)
	  val eq : t_sh -> t_sh -> bool
	  val string_of: t_sh -> string
	  val can_join : t_sh -> t_sh -> bool
	  val join : t_sh -> t_sh -> t_sh
	  val contains : t_sh -> t_sh -> bool
	  val subtract : t_sh -> t_sh -> t_sh
    end;;
 
module type SAT_SLV = functor (Sv : SV) ->
sig 
	type t_var = Sv.t
	type nz_cons = t_var list list
	type p_var
	type eq_syst = (t_var*t_var*p_var) list
	val call_sat:  nz_cons -> eq_syst -> bool
	val call_imply: t_var list -> nz_cons -> eq_syst -> t_var list -> nz_cons -> eq_syst -> (t_var*bool) list -> (t_var*t_var) list-> bool
	val mkTop : unit-> p_var
	(*val mkVar : t_var-> p_var*)
	val mkVar : t_var -> p_var
	val getVar : p_var -> t_var option
end;;
 
module type DFRAC_SOLVER =
  sig
	 type eq_syst
	 val is_sat : eq_syst -> bool
	 val imply : eq_syst -> eq_syst -> bool
	 val e_elim : eq_syst -> eq_syst
  end;;
  
  
(*functor (S:SV) -> functor (S2:SV with type t = S.t) -> *)
module Dfrac_s_solver = functor (Ts : TREE_CONST) -> functor (SV : SV)-> functor (Ss1 : SAT_SLV) ->
	struct
		module Ss= Ss1(SV)
		type t_var = SV.t
		type const_sh = Ts.t_sh
		type const_eq = t_var*const_sh
		type var_eq = t_var*t_var
		type frac_perm = 
			| Vperm of t_var 
			| Cperm of const_sh
		type eq = frac_perm * frac_perm * frac_perm

		type eq_syst = {
			eqs_ex : t_var list; 
			eqs_nzv : t_var list;
			eqs_vc : const_eq list;
			eqs_ve : var_eq list;
			eqs_eql : eq list;
		  } 
		
		(*todo consistency checks, reduce to the simple form with one constant*)
		exception Unsat_exception
		exception Unsat_conseq of bool
		
		let raise_us s = (*print_string ("exc: "^s^"\n");*) raise Unsat_exception
		let report_error s = failwith s 
		
		(*aux functions*)
		let fv f = match f with 
			| Vperm v -> [v]
			| _ -> []
		
		let mem_eq eq x l = List.exists (eq x) l
		let rec remove_dups_eq eq n =  match n with [] -> [] | q::qs -> if (mem_eq eq q qs) then remove_dups_eq eq qs else q::(remove_dups_eq eq qs)	
		
		let eq_fv (e1,e2,e3) = (fv e1)@(fv e2)@(fv e3)
		let eq_l_fv l = remove_dups_eq SV.eq (List.concat (List.map eq_fv l))
		let eq_sys_fv eqs = 
			let l1,l2 = List.split eqs.eqs_ve in
			remove_dups_eq SV.eq ((eq_l_fv eqs.eqs_eql)@ (fst (List.split eqs.eqs_vc))@l1@l2)
			
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
			
		let rename_ex eqs = 
			let sub = List.map (fun v-> (v, SV.fresh_var v)) eqs.eqs_ex in
			let ren_var v = try snd (List.find (fun (v1,_)-> SV.eq v v1) sub) with | Not_found -> v in
			let ren_v v = match v with | Vperm v-> Vperm (ren_var v) | _ -> v in
			let ren_eq (v1,v2,v3)= ren_v v1, ren_v v2, ren_v v3 in
			{	eqs_ex= snd (List.split sub);
				eqs_nzv = List.map ren_var eqs.eqs_nzv;
				eqs_ve = List.map (fun (v1,v2) -> ren_var v1,ren_var v2) eqs.eqs_ve ;
				eqs_vc = List.map (fun (v,c)-> ren_var v, c) eqs.eqs_vc;
				eqs_eql = List.map ren_eq eqs.eqs_eql;}
			
		let string_of_eq (v1,v2,v3) = 
			let f v = match v with | Vperm v -> SV.string_of v | Cperm t -> Ts.string_of t in
			(f v1)^ " * " ^(f v2) ^" = "^(f v3)
			
		let string_of_eq_l l = String.concat "\n" (List.map string_of_eq l)
			
		let pr_list f l = String.concat "\n" (List.map f l)
		let pr_list_s f l = String.concat " " (List.map f l)
		let pr_pair f1 f2 (e1,e2) = "("^(f1 e1)^" , "^f2 e2^")"
		let pr_quad f1 f2 f3 f4 (e1,e2,e3,e4) = "("^(f1 e1)^" , "^(f2 e2)^" , "^(f3 e3)^" , "^(f4 e4)^")"
		
		let string_of_vc_l l = pr_list (pr_pair SV.string_of Ts.string_of) l	
		
		let string_of_eq_syst eqs = 
			let seql = string_of_eq_l eqs.eqs_eql in
			let sve = String.concat "\n" (List.map (fun (v1,v2)-> (SV.string_of v1)^" = "^(SV.string_of v2)) eqs.eqs_ve) in
			let svc = string_of_vc_l eqs.eqs_vc in
			("exists: "^(pr_list_s SV.string_of eqs.eqs_ex)^"\n non-zeros: "^(pr_list_s SV.string_of eqs.eqs_nzv)^"\n"^svc^"\n"^sve^"\n"^seql)
			
			
		let rec check_const_incons vc_l = match vc_l with
				| [] -> ()
				| (v,c)::t -> 
					try 
						let _,c2 = List.find (fun (v2,_) -> SV.eq v v2) t in
						if c2 <> c then raise_us "const_inc"
						else check_const_incons t
					with Not_found ->check_const_incons t 
				
		let check_eq_incons ve_l = 
			List.iter (fun (e1,e2,e3)-> if Ss.getVar e3 = None & SV.eq e1 e2 then raise_us "eq_incons" else ()) ve_l
				
				
		let triv_subst vc vv t_vc t_ve (t_eq_l:eq list): var_eq list * (t_var*bool) list * eq list = 
			let sub_v_v (f,t) v = match v with | Cperm _ -> v | Vperm v1-> if (SV.eq f v1) then Vperm t else v in
			let sub_eq_v c (e1,e2,e3) = sub_v_v c e1, sub_v_v c e2, sub_v_v c e3 in			
			let sub_v_c (f,t) v = match v with | Cperm _ -> v | Vperm v1-> if (SV.eq f v1) then Cperm (if t then Ts.top else Ts.bot) else v in
			let sub_eq_c c (e1,e2,e3) = sub_v_c c e1,sub_v_c c e2,sub_v_c c e3 in		
			
			let t_vc,t_ve,t_eq_l = List.fold_left (fun (t_vc,t_ve,t_eq_l) (v1,v2)-> 
				let t_vc = List.map (fun (v,c)-> if SV.eq v v1 then v2,c else v,c) t_vc in
				let t_ve = List.map (fun (d1,d2)-> (if SV.eq v1 d1 then v2 else d1),(if SV.eq v1 d2 then v2 else d2)) t_ve in
				let t_eq_l = List.map (sub_eq_v (v1,v2)) t_eq_l in
				t_vc,t_ve,t_eq_l) (t_vc,t_ve,t_eq_l) vv in
				
			let t_vc,t_ve,t_eq_l = List.fold_left (fun (t_vc,t_ve,t_eq_l) (v , c)-> 
				let t_vc = List.filter (fun (v1,c1)-> if SV.eq v v1 then if c<>c1 then raise Unsat_exception else false else true) t_vc in
				let t_vc1,t_ve = List.fold_left (fun (a1,a2) (d1,d2)-> match SV.eq d1 v, SV.eq d2 v with 
					| false,false ->  a1,(d1,d2)::a2
					| true, false ->  (d2,c)::a1, a2
					| false, true ->  (d1,c)::a1, a2
					| _-> a1,a2) ([],[]) t_ve in
				let t_eq_l = List.map (sub_eq_c (v,c)) t_eq_l in
				t_vc@t_vc1,t_ve,t_eq_l) (t_vc,t_ve,t_eq_l) vc in
				
			t_ve,t_vc,t_eq_l
				
				
		let elim_exists sys = 
			let purge v sys = 
			{ sys with 
				eqs_nzv = List.filter (fun c-> not (SV.eq c v)) sys.eqs_nzv;
				eqs_vc = List.filter (fun (v1,_)-> not (SV.eq v1 v)) sys.eqs_vc;
				eqs_ve = List.filter (fun (v1,v2)-> not ((SV.eq v1 v) || (SV.eq v2 v))) sys.eqs_ve;} in
			List.fold_left (fun sys v-> 
				let eql = List.exists (SV.eq v) (eq_l_fv sys.eqs_eql) in
				let eqve = 
					let l1,l2 = List.split sys.eqs_ve in
					List.length (List.filter (SV.eq v) (l1@l2)) in
				let eqvc = List.length (List.filter (fun (v1,_) -> SV.eq v v1) sys.eqs_vc) in
				if not eql && (eqve+eqvc<=1) then (purge v sys)
				else {sys with eqs_ex= v::sys.eqs_ex}) {sys with eqs_ex = []} sys.eqs_ex
				
		let apl_substs (eqs:eq_syst):eq_syst =
			let rot (v1,v2) = if List.exists (SV.eq v2) eqs.eqs_ex then (v2,v1) else (v1,v2) in
			let eqs = {eqs with eqs_ve = List.map rot eqs.eqs_ve} in
			let eqs = 
			
			let rec helper eqs l_eqs = match l_eqs with
				| [] -> eqs
				| (v1,v2)::t ->
				let subst_e e = match e with | Vperm v -> if SV.eq v v1 then Vperm v2 else e | _ -> e in
				let t = List.map (fun (c1,c2)-> if SV.eq v1 c1 then (v2,c2) else if SV.eq v1 c2 then (v2,c1) else (c1,c2)) t in
				helper {eqs with 		
					eqs_ve = (v1,v2)::eqs.eqs_ve;
					eqs_vc = List.map (fun (v,c)-> if SV.eq v v1 then (v2,c) else (v,c)) eqs.eqs_vc ;
					eqs_nzv = remove_dups_eq SV.eq (List.map (fun v-> if SV.eq v v1 then v2 else v) eqs.eqs_nzv);
					eqs_eql = List.map (fun (e1,e2,e3)-> subst_e e1, subst_e e2, subst_e e3) eqs.eqs_eql ;
				} t in
				helper {eqs with eqs_ve=[]} eqs.eqs_ve in
			let rec subst_vc l_vc eqs = 
				if l_vc =[] then  eqs
				else
					let l_vc, l_eqs = List.fold_left (fun (lvc,l_eqs)(e1,e2,e3)-> 
						let subst e = match e with 
							| Vperm v1 -> (try Cperm (snd (List.find (fun (v,_)-> SV.eq v1 v) eqs.eqs_vc)) with | _ -> e)
							| _ -> e in
						let e1,e2,e3= subst e1, subst e2, subst e3 in
						match e1,e2,e3 with 
							| Cperm t1, Cperm t2, Cperm t3 -> if (Ts.can_join t1 t2)&& (Ts.eq (Ts.join t1 t2) t3) then lvc,l_eqs else raise Unsat_exception
							| Cperm t1, Cperm t2, Vperm v -> if (Ts.can_join t1 t2) then (v,Ts.join t1 t2)::lvc,l_eqs else raise Unsat_exception
							| Cperm t, Vperm v, Cperm tr 
							| Vperm v, Cperm t, Cperm tr -> if Ts.contains tr t  then (v,Ts.subtract tr t)::lvc,l_eqs else raise Unsat_exception 
							| _ ->  lvc,(e1,e2,e3)::l_eqs) ([],[]) eqs.eqs_eql in
					subst_vc l_vc {eqs with eqs_vc= eqs.eqs_vc@l_vc; eqs_eql = l_eqs} in
			let eqs = subst_vc eqs.eqs_vc eqs in
			let rec check_const_incons vc_l = match vc_l with | [] -> ()
				| (v,c)::t -> try 
					if Ts.eq c (snd (List.find (fun (v2,_) -> SV.eq v v2) t)) then check_const_incons t else raise Unsat_exception
					with Not_found ->check_const_incons t  in
			let nnzv = List.filter (fun nzv->not (List.exists (fun (v,_)-> SV.eq nzv v) eqs.eqs_vc)) eqs.eqs_nzv in
			check_const_incons eqs.eqs_vc; elim_exists {eqs with eqs_nzv = nnzv}
				
				
		(*let subst_a_eqs a_sys c_sys = 
			let rot (v1,v2) = if List.exists (SV.eq v2) a_sys.eqs_ex then (v2,v1) else (v1,v2) in
			let a_eqs_ve = List.map rot a_sys.eqs_ve in
			let a_eqs_vc = List.fold_left (fun a_eqs_vc (v1,v2)-> List.map (fun (v,c)-> if SV.eq v v1 then (v2,c) else (v,c)) a_eqs_vc) a_sys.eqs_vc a_eqs_ve in
			let a_sys = {a_sys with eqs_ve = a_eqs_ve; eqs_vc = a_eqs_vc} in
			let ave = List.filter (fun (v1,v2) -> not (List.exists (fun c-> SV.eq v1 c || SV.eq v2 c) a_sys.eqs_ex)) a_sys.eqs_ve in
			let avc = List.filter (fun (v1,_) -> not (List.exists (SV.v1) a_sys.eqs_ex)) a_sys.eqs_vc in
			let c_sys = {c_sys with }*)
				
		(*decomposition functions*)
		let gen_left_name n = n^"__L" 
		let gen_left_var v = SV.rename v (gen_left_name (SV.get_name v))
		
		let gen_right_name n = n^"__R" 
		let gen_right_var v = SV.rename v (gen_right_name (SV.get_name v))
		
		let eq_depth_0 ef = match ef with
			| Cperm d, Vperm _, Vperm _
			| Vperm _, Cperm d, Vperm _
			| Vperm _, Vperm _, Cperm d -> Ts.depth_0 d
			| Vperm _, Vperm _, Vperm _ -> true
			| _ -> report_error ("unexpected equation structure "^(string_of_eq ef)^"\n")
			
		let decompose_fp (f:frac_perm) = match f with 
			| Vperm vp -> 
				[vp], Vperm (gen_left_var vp), Vperm (gen_right_var vp)
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
		
		let rec decompose_vc (v,c) = 
			if Ts.depth_0 c then [],[(v,c)]
			else 
				let dv1,vc1 = decompose_vc (gen_left_var v, Ts.rleft c) in
				let dv2,vc2 = decompose_vc (gen_right_var v, Ts.rright c) in
				v::(dv1@dv2),vc1@vc2
			
		
		let decompose_sys eqs = 
			(*if a variable is decomposed in some eq, it will need to be decomposed in all eqs*)
			let rec one_pass b l_vs acc leqs = match leqs with
				| [] -> (b,l_vs,acc)
				| h::t -> 
					if List.exists (fun v1-> mem_eq SV.eq v1 l_vs) (eq_fv h) then 
						let lv,leq,req = decomp_no_lim h in
						one_pass true (l_vs@lv) acc (leq::req::t)
					else
					 one_pass b l_vs (h::acc) t in
			
			(*let rec one_pass_vc b l_vs acc leqs = match leqs with
				| [] -> (b,l_vs,acc)
				| (v,c)::t -> 
					if mem_eq SV.eq v l_vs then 
						let lv,leq,req = decomp_no_lim h in
						one_pass_vc true (l_vs@lv) acc (leq::req::t)
					else
					 one_pass_vc b l_vs (h::acc) t in*)
					 
			let rec fix_helper l_vs l_eqs = 
				let b,l_vs,l_eqs = one_pass false l_vs [] l_eqs in
				if b then fix_helper l_vs l_eqs 
				else (l_vs, l_eqs) in
				
			let extra_decomp decomp leqs  to_decomp = 	
				let to_decomp = List.map SV.get_name to_decomp in
				List.fold_left (fun (a,l) eq-> 
					if (List.exists (fun v-> 
						let nv = SV.get_name v in
						mem_eq BatString.starts_with nv to_decomp) (eq_fv eq)) then 
						let lv,leq,req = decomp_no_lim eq in
						lv@a,leq::req::l
					else a,eq::l) (decomp,[]) leqs in 
				
			let eqs = apl_substs eqs in
			let l_decomp_vs1, vc = fold_2_map decompose_vc eqs.eqs_vc in
			let eqs = {eqs with eqs_vc=vc} in
			let l_decomp_vs, leqs = fold_2_map decompose_eq eqs.eqs_eql in 
			let l_decomp_vs = l_decomp_vs@l_decomp_vs1 in
			let l_extra_decomp = List.filter (fun v-> not (List.exists (fun (v2,_)-> SV.eq v v2) eqs.eqs_vc)) eqs.eqs_nzv in
			let l_decomp_vs, leqs = extra_decomp l_decomp_vs leqs l_extra_decomp in
			(*due to substs, no need to decompose vc nor ve, if need be, it will happen in the imply during the meet*)
			let l_decomp_vs, leqs = fix_helper l_decomp_vs leqs in
			let l_decomp_vs = remove_dups_eq SV.eq l_decomp_vs in
			let vc = List.map (fun (v,c)-> v, if Ts.full c then true else if Ts.empty c then false else report_error ("unexpected constant"^(Ts.string_of c))) eqs.eqs_vc in
			l_decomp_vs, eqs.eqs_nzv, eqs.eqs_ve, vc, leqs
		
		let decompose_sys eqs = 
			(*print_string ("decompose syst: " ^ (string_of_eq_syst eqs)^"\n");*)
			let (r1,r2,r3,r4,r5) = decompose_sys eqs in
			(*print_string ("decomposed syst: \n dec vars: " ^(pr_list_s SV.string_of r1)^
						  "\n nzv list: "^(pr_list_s SV.string_of r2)^
						  "\n v eqs: "^(pr_list (pr_pair SV.string_of SV.string_of ) r3)^
						  "\n vconsts: "^ (pr_list (pr_pair SV.string_of string_of_bool)r4)^
						  "\n eqs: "^(string_of_eq_l r5)^"\n");*)
			(r1,r2,r3,r4,r5)
		
		
		let all_decomps_1 l_decs v = (*returns only the leafs of the decompositions*)
			let rec fp v = if mem_eq SV.eq v l_decs then (fp (gen_left_var v))@(fp (gen_right_var v)) else [v] in
			if mem_eq SV.eq v l_decs then (fp (gen_left_var v))@(fp (gen_right_var v)) else [] 
		
		let all_decomps_2 l_decs v = (*returns only the leafs of the decompositions*)
			let rec fp v = if mem_eq SV.eq v l_decs then (fp (gen_left_var v))@(fp (gen_right_var v)) else [v] in
			fp v
		
		let all_decomps_l l_decs vl = 
			(*let pr1 = pr_list_s SV.string_of in*)
			(*let _ = print_string ("all_decomps_l in1: "^(pr1 l_decs)^"\n all_decomps_l in2: "^(pr1 vl)^"\n") in*)
			let r = fold_1_map (all_decomps_2 l_decs) vl in
			(*let _ = print_string ("all_decomps_l  out: "^(pr1 r)^"\n") in*)
			r
		
		let longest_subst lst a dec_v = 
			(*find if there exists some var that needs decomposition in lst to get to v*)
			(*finds the largest substring*)
			let nv = SV.get_name dec_v in
			let lnv = String.length nv in
			let ac = List.fold_left (fun ac v-> 
				let nvv = SV.get_name v in
				let lnvv = String.length nvv in
				if lnv=lnvv then ac 
				else 
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
				
		let meet_decompositions (avl,(ave:var_eq list),(avc: (t_var*bool) list),ael) (cvl,(cve:var_eq list),(cvc:(t_var*bool) list),cel) int_vs
		 : t_var list * eq list * var_eq list * (t_var*bool) list * t_var list * var_eq list * (t_var*bool) list * eq list=  
			let expand vl ve vc el exp_l = 
				let expand_one (vl,ve, vc, el) v = 
					let expand_one_one_acc (nvl,eq_acc) eq = 
						if mem_eq SV.eq v (eq_fv eq) then 
							let lv,leq,req = decomp_no_lim eq in
							lv@nvl, leq::req::eq_acc 
						else (nvl,eq::eq_acc) in
					let expand_one_ve (vl, ve_acc) (v1,v2) =
						if SV.eq v v1 || SV.eq v v2 then 
						  v1::v2::vl, (gen_left_var v1,gen_left_var v2):: (gen_right_var v1, gen_right_var v2)::ve_acc
						else vl,(v1,v2)::ve_acc in
					let expand_one_vc (vl, vc_acc) (v1,c) =
						if SV.eq v v1  then 
						  v1::vl, (gen_left_var v1, c):: (gen_right_var v1, c)::vc_acc
						else vl,(v1,c)::vc_acc in
						
					let nvl, el = List.fold_left expand_one_one_acc ([],[]) el in
					let nvle, ve = List.fold_left expand_one_ve ([],[]) ve in
					let nvlc, vc = List.fold_left expand_one_vc ([],[]) vc in
					remove_dups_eq SV.eq (vl@nvl@nvle@nvlc), ve,vc,el in			
				List.fold_left expand_one (vl,ve,vc,el) exp_l in
									
			let rec fix (avl,ave,avc,ael) (cvl,cve,cvc,cel) a_int_vs (*decomposed in ante*) c_int_vs (*decomposed in conseq*) =
				(*let _ = print_string ("avl "^( pr_list_s SV.string_of avl)^"\n") in
				let _ = print_string ("cvl "^( pr_list_s SV.string_of cvl)^"\n") in
				let _ = print_string ("a_int_vs "^( pr_list_s SV.string_of a_int_vs)^"\n") in
				let _ = print_string ("c_int_vs "^( pr_list_s SV.string_of c_int_vs)^"\n") in*)
				let c_exp = remove_dups_eq SV.eq (List.fold_left (longest_subst c_int_vs) [] a_int_vs) in (*what needs decomposing in conseq*)
				let a_exp = remove_dups_eq SV.eq (List.fold_left (longest_subst a_int_vs) [] c_int_vs) in (*what needs decomposing in ante*)
				if a_exp=[] && c_exp=[] then avl,ael,ave,avc,cvl,cve,cvc,cel
				else
					(*let _ = print_string ("c_exp "^( pr_list_s SV.string_of c_exp)^"\n") in
					let _ = print_string ("a_exp "^( pr_list_s SV.string_of a_exp)^"\n") in*)
					let avl,ave,avc,ael = expand avl ave avc ael a_exp in
					let cvl,cve,cvc,cel = expand cvl cve cvc cel c_exp in
					fix (avl,ave,avc,ael) (cvl,cve,cvc,cel) (all_decomps_l avl a_int_vs) (all_decomps_l cvl c_int_vs) in
			fix (avl,ave,avc,ael) (cvl,cve,cvc,cel) (all_decomps_l avl int_vs) (all_decomps_l cvl int_vs)
			
		let meet_decompositions ante conseq int_vs = 
		(*let pr_vl = pr_list_s SV.string_of in
		let pr_vel = pr_list_s (pr_pair SV.string_of SV.string_of) in
		let pr_vcl = pr_list_s (pr_pair SV.string_of string_of_bool) in
		let pr1 = pr_quad pr_vl pr_vel pr_vcl string_of_eq_l in
		let _ = print_string ("meet_decompositions IN1: "^(pr1 ante)^"\n meet_decompositions IN2: "^(pr1 conseq)^"\n meet_decompositions IN3: "^(pr_vl int_vs)^"\n");flush_all () in*)
		let a_dec_vars, a_l_eqs, a_v_e, a_v_c, c_dec_vars,  c_v_e, c_v_c, c_l_eqs = meet_decompositions ante conseq int_vs in
		(*let rante = a_dec_vars, a_v_e, a_v_c, a_l_eqs in
		let rconseq =  c_dec_vars, c_v_e, c_v_c, c_l_eqs in
		let _ = print_string ("meet_decompositions OUT1: "^(pr1 rante)^"\n meet_decompositions OUT2: "^(pr1 rconseq)^"\n");flush_all () in*)
		a_dec_vars, a_l_eqs, a_v_e, a_v_c, c_dec_vars,  c_v_e, c_v_c, c_l_eqs
		
		(*simplification  functions, reductions to v*v=v*)
		let compute_nz_cons nzv decomp_vs vc_l ve_l  = 
			let nz_cons = List.map (fun c-> let t = all_decomps_1 decomp_vs c in if t=[] then [c] else t) nzv in 
			let nz_cons = List.fold_left (fun nz (f,t) -> List.map (subst_ex_l (f,t)) nz) nz_cons ve_l in
			let nz_cons	= List.fold_left (fun nz (v,c) -> 
				if c then List.filter (fun d-> not (mem_eq SV.eq v d)) nz
				else List.map (fun d-> List.filter (fun v1-> not (SV.eq v v1)) d) nz) nz_cons vc_l in
			if (List.exists (fun c-> c=[]) nz_cons) then raise_us "nz_cons"
			else (*List.map (List.map SV.conv)*) nz_cons 
		
		let tree_v_solver ex_l e = match e with
			| Cperm d, Vperm v1, Vperm v2 
			| Vperm v1, Cperm d, Vperm v2 -> 
				if Ts.empty d then if mem_eq SV.eq v2 ex_l then ([],[(v2,v1)],[]) else ([],[(v1,v2)],[])
				else if Ts.full d then ([(v1,Ts.bot);(v2,Ts.top)],[],[]) else [],[],[e]
			| Vperm v1, Vperm v2, Cperm d -> if Ts.empty d then ([(v1,Ts.bot);(v2,Ts.bot)],[],[]) else ([],[],[e])
			| Cperm d1, Cperm d2, Vperm v -> if (Ts.can_join d1 d2) then  [(v,Ts.join d1 d2)],[],[] else raise Unsat_exception
			| Cperm d1, Vperm v, Cperm d2 
			| Vperm v, Cperm d1, Cperm d2  -> if (Ts.contains d2 d1) then  [(v,Ts.subtract d2 d1)],[],[] else raise Unsat_exception
			| Cperm d1, Cperm d2, Cperm d3 -> if (Ts.can_join d1 d2) && (Ts.eq (Ts.join d1 d2) d3) then [],[],[] else raise Unsat_exception
			| Vperm v1, Vperm v2, Vperm v3 -> 
				if SV.eq v1 v2 then [(v1,Ts.bot);(v2,Ts.bot);(v3,Ts.bot)],[],[]
				else if SV.eq v1 v3 then [(v2,Ts.bot)],[],[] 
				else if SV.eq v2 v3 then [(v1,Ts.bot)],[],[]
				else [],[],[e]

		let simpl_vars r1 r2 r3 = 
			if SV.eq r1 r2 then [(r1,false);(r3,false)],[]
			else if SV.eq r1 r3 then [(r2,false)],[] 
			else if SV.eq r2 r3 then [(r1,false)],[] 
			else [],[(r1,r2,Ss.mkVar r3)]
			
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
				else ([],[],[(v1,v2,Ss.mkTop ())])
				(*if Ts.full d then else report_error "incomplete decomposition"*)
			| Cperm d1, Cperm d2, Vperm v -> 
				if (Ts.full d1)&&(Ts.full d2) then raise_us "c_v_solver_3" else ([(v,Ts.full d1 || Ts.full d2)],[],[])
			| Cperm d1, Vperm v, Cperm d2 
			| Vperm v, Cperm d1, Cperm d2 -> (match Ts.full d2,Ts.full d1 with 
				| true, true -> ([(v,false)],[],[])
				| true, false -> ([(v,true)],[],[])
				| false, false -> ([(v,false)],[],[])
				| false, true -> raise_us "c_v_solver_2")
			| Vperm v1, Vperm v2, Vperm v3 -> let r1,r2 = simpl_vars v1 v2 v3 in (r1,[],r2)
			| Cperm d1, Cperm d2, Cperm d3 -> 
				let fd1 = Ts.full d1 in
				let fd2 = Ts.full d2 in
				let fd3 = Ts.full d3 in
				if (not (fd1 && fd2) && fd3=(fd1||fd2)) then ([],[],[]) else raise_us "c_v_solver_1"
					
			
		let rec appl_substs exvl consts subs eqs =
			let ex_subst v1 v2 = if mem_eq SV.eq v2 exvl then (v2,v1) else (v1,v2) in
			let subst_ex_eq p (v1,v2,v3) = 
				let r1 = subst_ex p v1 in
				let r2 = subst_ex p v2 in
				match Ss.getVar v3 with  
				| None -> if SV.eq r1 r2 then raise_us "subst_ex_eq" else ([],[(r1,r2,Ss.mkTop ())])
				| Some v -> simpl_vars r1 r2 (subst_ex p v(*(SV.rconv v)*)) in
					
			let solve_2 (v,c) (v1,v2,v3s) = 
				let s1 = SV.eq v1 v in
				let s2 = SV.eq v2 v in
				match Ss.getVar v3s with 
					| None -> (match s1,s2 with
						| true, true -> raise_us "solve_2_2"
						| false,false ->([],[],[(v1,v2,v3s)])
						| true, false ->([v2,not c],[],[])
						| false, true ->([v1,not c],[],[]))
					| Some v3t->
						let v3 = (*SV.rconv*) v3t in
						let s3 = SV.eq v3 v in
						(match s1,s2,s3,c with 
							| true,true,_,true -> raise_us "solve_2_1"
							| true,true,true, false -> ([],[],[])
							| true,true,false, false -> ([v3,c],[],[])
							| false,false,true,true-> ([],[],[(v1,v2,Ss.mkTop ())]) 
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
			
				
		let solve_trivial_eq_l ex_l l_ve (l_vc:(t_var*bool) list) l = 	
			(*first pass: reduces eq syst to v=c , v=v, v+v=(v|1) *)
			let l_c, l_s, l_e = fold_3_map (c_v_solver ex_l) l in
			(*second pass, apply subst until fixpoint is reached*)
			let l_c, l_s, l_e = appl_substs ex_l (l_c@l_vc) (l_s@l_ve) l_e in
			check_const_incons l_c;
			check_eq_incons l_e;
			l_c, l_s, l_e
		
		(*let conv_eq_s = List.map (fun (e1,e2,c)-> (SV.conv e1, SV.conv e2, c))*)
		let call_sat nz l_eqs = 
		 (* let pr_vl c= "[ "^(pr_list_s SV.string_of c)^" ]\n "in
		  let pr_eq (v1,v2,v3) = SV.string_of v1 ^" + "^(SV.string_of v2)^ " = " ^(match Ss.getVar v3 with | None -> "true" | Some v-> SV.string_of v) in
   		  print_string ("sat: nz: "^(pr_list pr_vl nz)^"eqs:"^(pr_list pr_eq l_eqs));flush_all ();*)
		  Ss.call_sat nz l_eqs 
		
		let is_sat (eqs : eq_syst): bool = 			
		    if eqs.eqs_eql=[] then (check_const_incons (apl_substs eqs).eqs_vc; true)
			else
				try
					(*decomposes the vars, returns the simplified syst to v*v=(v|1) and non-zero constraints*)
					let const_vars, subst_vars,l_eqs = fold_3_map (tree_v_solver eqs.eqs_ex) eqs.eqs_eql in
					let eqs = {eqs with eqs_eql = l_eqs; eqs_ve = subst_vars@eqs.eqs_ve; eqs_vc = const_vars@eqs.eqs_vc} in
					let dec_vars,nzv, _,_,eqs = decompose_sys eqs in
					let const_vars, subst_vars,l_eqs = solve_trivial_eq_l [] [] [] eqs in
					let nz_cons = compute_nz_cons nzv dec_vars const_vars subst_vars in
					if l_eqs = [] then true else call_sat nz_cons ((*conv_eq_s*) l_eqs)
				with Unsat_exception -> false
				
		let is_sat (eqs:eq_syst):bool = 
			(*print_string ("Big Sat: "^(string_of_eq_syst eqs)^"\n");*)
			let r = is_sat eqs in
			(*print_string ("Big Sat Res: "^(string_of_bool r)^"\n");*) r
		
			
		let call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars = 
		 (* let pr_vl c= "[ "^(pr_list_s SV.string_of c)^" ]\n "in
		  let pr_sub (v1,v2) = (SV.string_of v1)^" = "^(SV.string_of v2) in
		  let pr_cns (v1,b) = (SV.string_of v1)^" = "^(string_of_bool b) in
		  let pr_eq (v1,v2,v3) = SV.string_of v1 ^" + "^(SV.string_of v2)^ " = " ^(match Ss.getVar v3 with | None -> "true" | Some v-> SV.string_of v) in
		  let print_syst ev nz eqs cns sub=
			print_string ("ev: "^(pr_vl ev)^"nz: "^(pr_list pr_vl nz)^"\n eqs:"^(pr_list pr_eq eqs)^"\n cns: "^(pr_list pr_cns cns)^"\nsub: "^(pr_list pr_sub sub)^"\n")	 in
		  print_syst a_ev a_nz_cons a_l_eqs [] [] ;
		  print_syst c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars ;flush_all ();*)
		  Ss.call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars
			
		let to_formula_imply a_sys c_sys:bool =
			(*decomposes the vars, returns the list of decomposed vars, var subst, var instantiations, simplified syst to v*v=(v|1) for both ante and conseq *)

			(*rename existentials to avoid clashes*)
			let a_sys = rename_ex a_sys in
			let c_sys = rename_ex c_sys in
			
			(*let a_sys, c_sys = subst_a_eqs a_sys c_sys in*)
			
			(*intersection variables*)
			let int_fv = 
				let afv = eq_sys_fv a_sys in
				let cfv = eq_sys_fv c_sys in
				List.filter (fun v-> mem_eq SV.eq v cfv) afv in
				
			(*decompose each system*)
			
			let c_d_vs, c_nzv, c_v_e, c_v_c, c_l_eqs = try 
				let const_vars, subst_vars,l_eqs = fold_3_map (tree_v_solver c_sys.eqs_ex) c_sys.eqs_eql in
				let c_sys = {c_sys with eqs_eql = l_eqs; eqs_ve = subst_vars@c_sys.eqs_ve; eqs_vc = const_vars@c_sys.eqs_vc} in	
				decompose_sys c_sys with | Unsat_exception -> raise (Unsat_conseq (not (is_sat a_sys))) in
				
			let a_d_vs, a_nzv, a_v_e, a_v_c, a_l_eqs = 
				let const_vars, subst_vars,l_eqs = fold_3_map (tree_v_solver a_sys.eqs_ex) a_sys.eqs_eql in
				let a_sys = {a_sys with eqs_eql = l_eqs; eqs_ve = subst_vars@a_sys.eqs_ve; eqs_vc = const_vars@a_sys.eqs_vc} in
				decompose_sys a_sys in

			(*further decompose both until each var is at the same level of decomposition*)
			let a_dec_vars, a_l_eqs, a_v_e, a_v_c, c_dec_vars,  c_v_e, c_v_c, c_l_eqs =  meet_decompositions  (a_d_vs,a_v_e, a_v_c,a_l_eqs)  (c_d_vs, c_v_e, c_v_c, c_l_eqs) int_fv in
			
			(*decomp the existentials as well*)
			let a_ev = List.fold_left (fun a c-> a@(all_decomps_1 a_dec_vars c)) [] a_sys.eqs_ex in
			let c_ev = List.fold_left (fun a c-> a@(all_decomps_1 c_dec_vars c)) [] c_sys.eqs_ex in
			
			(*simplify the antecedent*)
			let a_const_vars, a_subst_vars, a_l_eqs = solve_trivial_eq_l a_ev a_v_e a_v_c a_l_eqs in
			let a_nz_cons = compute_nz_cons a_nzv a_dec_vars a_const_vars a_subst_vars in
			
			(*apply the substitutions from the antecedent to the conseq*)
			try
				let c_v_e, c_v_c, c_l_eqs = triv_subst a_const_vars a_subst_vars c_v_c c_v_e c_l_eqs in
			
			(*simplify the conseq*)
			
				let c_const_vars, c_subst_vars, c_l_eqs = solve_trivial_eq_l c_ev c_v_e c_v_c c_l_eqs in
				let c_nz_cons = compute_nz_cons c_nzv c_dec_vars c_const_vars c_subst_vars in
				(*let c_const_vars = List.map (fun (v,c)-> SV.conv v,c) c_const_vars in
				let c_subst_vars = List.map (fun (v1,v2)-> SV.conv v1, SV.conv v2) c_subst_vars in
				let a_ev = List.map SV.conv a_ev in
				let c_ev = List.map SV.conv c_ev in
				let a_l_eqs = conv_eq_s a_l_eqs in
				let c_l_eqs = conv_eq_s c_l_eqs in*)
				if c_l_eqs=[] && c_const_vars=[] && c_subst_vars=[] then true
				else call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars
			with | Unsat_exception -> not (call_sat a_nz_cons ((*conv_eq_s*) a_l_eqs))
			
				
		let imply  (a_sys : eq_syst) (c_sys : eq_syst) : bool = 
			if c_sys.eqs_eql=[]&&c_sys.eqs_ve=[]&&c_sys.eqs_vc=[] then true
			else
				try
					to_formula_imply a_sys c_sys 
				with 
				 | Unsat_exception -> true
				 | Unsat_conseq b -> b
		
		let imply  (a_sys : eq_syst) (c_sys : eq_syst) : bool = 
			(*print_string ("Big Imply1: "^(string_of_eq_syst a_sys)^"\n");
			print_string ("Big Imply2: "^(string_of_eq_syst c_sys)^"\n");*)
			let r = imply a_sys c_sys in
			(*print_string ("Big Imply Res: "^(string_of_bool r)^"\n");*)  r
		
		let e_elim (eqs : eq_syst) : eq_syst = eqs
		
end;;

	

(*concrete modules*)	

module Ts = Tree_shares.Ts
module Sv = 
  struct
	type t=string
	(*type t_spec = string
	let conv v=v
	let rconv v=v*)
	let cnt = ref 1
	let eq v1 v2 = (String.compare v1 v2) = 0
    let string_of v1 = v1
	(*let string_of_s v1 = v1
	let get_name_s v = v*)
	let rename _ s = s
    let get_name v = v	
	let var_of v = v
    let fresh_var _ = cnt:=!cnt+1; "ts_fv_"^(string_of_int !cnt)    
end

module Ss_triv:SAT_SLV = functor (Sv:SV) ->
  struct
	type t_var = Sv.t
	type nz_cons = t_var list list 
	type p_var = (*include Gen.EQ_TYPE with type t=v*)
		| PVar of t_var 
		| C_top
	type eq_syst = (t_var*t_var*p_var) list
	let call_sat _ _ = true 
	let call_imply _ _ _ _ _ _ _ _  = false 
	let mkTop () = C_top
	let mkVar v = PVar v
	let getVar v = match v with | C_top -> None | PVar v -> Some v
end;;

(*module Solver = Dfrac_s_solver(Ts)(Sv)(Ss_triv)*)
