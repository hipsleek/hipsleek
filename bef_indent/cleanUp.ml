#include "xdebug.cppo"
open Globals
open VarGen

module CF=Cformula
module CP=Cpure

 let rec split_eq v2elim l (keep,elim1,elim2) = match l with	
	| [] -> (keep,elim1,elim2)
	| (v1,v2)::rest -> 
		let elim_v1 = Gen.BList.mem_eq CP.eq_spec_var v1 v2elim  in
		let elim_v2 = Gen.BList.mem_eq CP.eq_spec_var v2 v2elim  in
		match elim_v1,elim_v2 with
			| true, true  -> split_eq v2elim rest (keep, elim1, (v1,v2)::elim2)
			| true, false -> split_eq v2elim rest (keep, (v1,v2)::elim1, elim2)
			| false, true -> split_eq v2elim rest (keep, (v2,v1)::elim1, elim2)
			| false,false -> split_eq v2elim rest ((v1,v2)::keep, elim1, elim2)	

 let get_substs v2elim alias = 
	let keep,elim1,elim2 = split_eq v2elim alias ([],[],[]) in
	let elim = List.fold_left (fun a (v1,v2)-> 
		let a = List.map (fun (c1,c2)-> if CP.eq_spec_var c1 v1 then (v2,c2) else (c1,c2)) a  in
		(v1,v2)::a) elim1 elim2 in
	keep,elim
	
 let get_new_vars ante_fv conseq_fv = 
   let term_str = Str.regexp "_[0-9]+$" in
   fst(List.fold_left (fun (l,cnt) c-> 
	   try 
		let ct,cn,cp = match c with | CP.SpecVar (a,b,c) -> a,b,c in
		let cn = Str.string_before cn (Str.search_forward term_str cn 0) in
		let suf = 
			if cnt<25 then Char.escaped(Char.chr((Char.code 'a')+cnt))
			else (string_of_int cnt)^"r" in
		let f_v = CP.SpecVar (ct,cn^"_"^suf,cp) in
		(c,f_v)::l,cnt+1
	   with Not_found -> l,cnt) ([],0) (ante_fv @conseq_fv))
	
(*for printing purposes*)
let cleanUpFormulas_x (ante:CF.formula) (conseq:CF.formula) : (CF.formula*CF.formula) = 
	if not !print_clean_flag then (ante,conseq)
	else 
		if (CF.is_or_formula ante || CF.is_or_formula conseq) then (ante,conseq)
		else 
			(*  H_lhs & p1 |- ex v . H_rhs & p2*)
			let aev, ah, ap, avp, _, _, _, _, pos = CF.all_components ante in
			let cev, ch, cp, cvp, _, _, _, _, _ = CF.all_components conseq in
			let a_fv = CF.fv ante in
			let com_vars = Gen.BList.intersect_eq CP.eq_spec_var a_fv (CF.fv conseq) in
			let a_h_fv = CF.h_fv ah in
			let v2elim = Gen.BList.difference_eq CP.eq_spec_var a_fv (com_vars@a_h_fv) in
			let a_alias,ap = Mcpure.get_all_vv_eqs_mix ap in
			let keep,elim = get_substs v2elim a_alias in
			let ap = List.fold_left (fun a (v1,v2)-> Mcpure.memoise_add_pure_N a (CP.mkEqVar v1 v2 pos)) ap keep in
			let ante = CF.mkBase ah ap avp CF.TypeTrue (CF.mkTrueFlow ()) [] pos in
			let ante = CF.subst elim ante in
			(*let conseq = subst fr t conseq in*)
			let svs = get_new_vars (CF.fv ante) (CF.fv conseq) in
			CF.subst_all svs ante, CF.subst_all svs conseq 

let cleanUpFormulas (ante:CF.formula) (conseq:CF.formula) : (CF.formula*CF.formula) = 
	let pr = !CF.print_formula in
Debug.no_2 "cleanUpFormulas" pr pr (Gen.pr_pair pr pr) cleanUpFormulas_x ante conseq



let cleanUpPureFormulas_x (ante:CP.formula) (conseq:CP.formula) : (CP.formula*CP.formula) = 
	if not !print_clean_flag then (ante,conseq)
	else 
		let a_fv = CP.fv ante in
		let com_vars = Gen.BList.intersect_eq CP.eq_spec_var a_fv (CP.fv conseq) in
		let v2elim = Gen.BList.difference_eq CP.eq_spec_var a_fv com_vars in
		let a_alias,ante = CP.get_all_vv_eqs ante in
		let keep,elim = get_substs v2elim a_alias in
		let ante = List.fold_left (fun a (v1,v2)-> CP.mkAnd a (CP.mkEqVar v1 v2 no_pos) no_pos) ante keep in
		let ante = CP.subst elim ante in
		(*let conseq = subst fr t conseq in*)
		let svs = get_new_vars (CP.all_vars ante) (CP.all_vars conseq) in
		CP.apply_subs_all svs ante, CP.apply_subs_all svs conseq

let cleanUpPureFormulas (ante:CP.formula) (conseq:CP.formula) : (CP.formula*CP.formula) = 
	let pr = !CP.print_formula in
Debug.no_2 "cleanUpFormulas" pr pr (Gen.pr_pair pr pr) cleanUpPureFormulas_x ante conseq





