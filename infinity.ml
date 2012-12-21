(* Created on 20th Dec 2012 by asankhs to handle Infinity *)

open Globals
open Gen.Basic
open Cprinter

module CP = Cpure
module MCP = Mcpure
module DD = Debug


(* Equisatisfiable Normalization *)
(* 
   v<=\inf      ==> true
   v>=\inf      ==> v=\inf
   v<=-\inf     ==> -v>=\inf
   v>=-\inf     ==> -v<=\inf
   min(w,\inf)  ==> w
   min(w,-\inf) ==> -\inf
   max(w,\inf)  ==> \inf
   max(w,-\inf) ==> w
   v<inf        ==> not(v=inf)
   v>inf        ==> false
   v<-inf       ==> -v>inf
   v>-inf       ==> -v<inf 
*)

let rec normalize_exp (exp: CP.exp) : CP.exp =
  let _ = DD.vv_trace("in normalize_exp: "^ (string_of_formula_exp exp)) in
  match exp with
    | CP.Min(e1,e2,pos) -> let e1_norm = normalize_exp e1 in
                           let e2_norm = normalize_exp e2 in
                           if CP.is_const_or_var e1_norm && CP.is_inf e2_norm
                           then e1_norm
                           else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm
                           then e2_norm
                           else CP.Min(e1_norm,e2_norm,pos)
    | CP.Max(e1,e2,pos) -> let e1_norm = normalize_exp e1 in
                           let e2_norm = normalize_exp e2 in
                           if CP.is_const_or_var e1_norm && CP.is_inf e2_norm
                           then e2_norm
                           else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm
                           then e1_norm
                           else CP.Max(e1_norm,e2_norm,pos)
    | CP.Add(e1,e2,pos) -> let e1_norm = normalize_exp e1 in
    			   let e2_norm = normalize_exp e2 in
    			   if CP.is_const_or_var e1_norm && CP.is_inf e2_norm
    			   then e2_norm
    			   else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm
    			   then e1_norm
    			   else CP.Add(e1_norm,e2_norm,pos)                          
    | _ -> exp


let check_neg_inf (exp1: CP.exp) (exp2: CP.exp) (exp3: CP.exp) : bool * CP.exp * CP.exp = 
match exp1 with
 | CP.Add(a1,a2,pos) -> let oexp = if CP.is_inf a1 then a2 else 
 			           if CP.is_inf a2 then a1 else exp1 in
  	(match exp2 with
    	| CP.Add(e1,e2,pos) -> let flag = if CP.is_inf e1 || CP.is_inf e2 
    			   then if CP.is_int exp3
    			   then (match exp3 with
    			   	| CP.IConst(b,_) -> if b == 0 then true else false
    			   	| _ -> false)
    			   else false
    			   else false
    			   in let exp = if CP.is_inf e1 then e2 else 
    			   	if CP.is_inf e2 then e2 else exp2
    			   in flag,oexp,exp
    	| _ -> match exp3 with
    	     	| CP.Add(e1,e2,pos) -> let flag = if CP.is_inf e1 || CP.is_inf e2 
    			   	   then if CP.is_int exp2
      			           then (match exp2 with
				   	| CP.IConst(b,_) -> if b == 0 then true else false
    				   	| _ -> false)
    				   else false
    				   else false
    				   in let exp = if CP.is_inf e1 then e1 else 
    			   	   if CP.is_inf e2 then e2 else exp3
    			  	   in flag,oexp,exp
    	     	| _ -> false,exp2,exp3)
 | _ -> false,exp2,exp3

let rec normalize_b_formula (bf: CP.b_formula) :CP.b_formula = 
  let _ = DD.vv_trace("in normalize_b_formula: "^ (string_of_b_formula bf)) in
  let (p_f,bf_ann) = bf in
  let p_f_norm = 
  (match p_f with
    | CP.Lt(e1,e2,pos) -> let e1_norm = normalize_exp e1 in
                          let e2_norm = normalize_exp e2 in
                          if CP.is_const_or_var e1_norm && CP.is_inf e2_norm 
                          then CP.Neq(e1_norm,e2_norm,pos)
                          else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm
                          then CP.BConst(false,pos)
                          else CP.Lt(e1_norm,e2_norm,pos)
    | CP.Lte(e1,e2,pos) -> let e1_norm = normalize_exp e1 in
                           let e2_norm = normalize_exp e2 in
                           if CP.is_const_or_var e1_norm && CP.is_inf e2_norm 
                           then CP.BConst(true,pos)
                           else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm
                           then CP.Eq(e1_norm,e2_norm,pos)
                           else CP.Lte(e1_norm,e2_norm,pos)
    | CP.Gt(e1,e2,pos) -> let e1_norm = normalize_exp e1 in
                          let e2_norm = normalize_exp e2 in
                          if CP.is_const_or_var e1_norm && CP.is_inf e2_norm 
                          then CP.BConst(false,pos)
                          else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm
                          then CP.Neq(e1_norm,e2_norm,pos)
                          else CP.Gt(e1_norm,e2_norm,pos)
    | CP.Gte(e1,e2,pos) -> let e1_norm = normalize_exp e1 in
                           let e2_norm = normalize_exp e2 in
                           if CP.is_const_or_var e1_norm && CP.is_inf e2_norm 
                           then CP.Eq(e1_norm,e2_norm,pos)
                           else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm
                           then CP.BConst(true,pos)
                           else CP.Gte(e1_norm,e2_norm,pos)
    | CP.Eq (e1,e2,pos) -> let e1_norm = normalize_exp e1 in
                           let e2_norm = normalize_exp e2 in
                           CP.Eq(e1_norm,e2_norm,pos)
    | CP.Neq (e1,e2,pos) -> let e1_norm = normalize_exp e1 in
                            let e2_norm = normalize_exp e2 in
                            CP.Neq(e1_norm,e2_norm,pos)                            
    | CP.EqMax (e1,e2,e3,pos) -> let flag,w1,w2 = check_neg_inf e1 e2 e3 in
			         if flag then CP.Eq(w1,w2,pos)
			         else
			         let e1_norm = normalize_exp e1 in
                                 let e2_norm = normalize_exp e2 in
                                 let e3_norm = normalize_exp e3 in
                                 if CP.is_const_or_var e2_norm && CP.is_inf e3_norm 
                                 then CP.Eq(e1_norm,e3_norm,pos)
                                 else if CP.is_inf e2_norm && CP.is_const_or_var e3_norm
                                 then CP.Eq(e1_norm,e2_norm,pos)                                
                                 else CP.EqMax(e1_norm,e2_norm,e3_norm,pos)
    | CP.EqMin (e1,e2,e3,pos) -> let flag,w1,w2 = check_neg_inf e1 e2 e3 in
			         if flag then CP.Eq(e1,(CP.mkIConst 0 pos),pos)
			         else 
			         let e1_norm = normalize_exp e1 in   
                                 let e2_norm = normalize_exp e2 in
                                 let e3_norm = normalize_exp e3 in
                                 if CP.is_const_or_var e2_norm && CP.is_inf e3_norm 
                                 then CP.Eq(e1_norm,e2_norm,pos)
                                 else if CP.is_inf e2_norm && CP.is_const_or_var e3_norm
                                 then CP.Eq(e1_norm,e3_norm,pos)
                                 else CP.EqMin(e1_norm,e2_norm,e3_norm,pos)
    | _ -> p_f
  ) in  let _ = DD.vv_trace("in normalized_b_formula: "^ (string_of_b_formula (p_f_norm,bf_ann))) in
 (p_f_norm,bf_ann)

let rec normalize_formula (pf: CP.formula) : CP.formula = 
  let _ = DD.vv_trace("in normalize_formula: "^ (string_of_pure_formula pf)) in
  (match pf with 
    | CP.BForm (b,fl) -> let b_norm = normalize_b_formula b in CP.BForm(b_norm,fl) 
    | CP.And (pf1,pf2,pos) -> let pf1_norm = normalize_formula pf1 in
                              let pf2_norm = normalize_formula pf2 in
                              CP.And(pf1_norm,pf2_norm,pos) 
    | CP.AndList pflst -> let pflst_norm = List.map 
                            (fun (sl,pf) -> (sl,normalize_formula pf)) pflst in CP.AndList(pflst_norm)
    | CP.Or (pf1,pf2,fl,pos) -> let pf1_norm = normalize_formula pf1 in
                                let pf2_norm = normalize_formula pf2 in
                                CP.Or(pf1_norm,pf2_norm,fl,pos) 
    | CP.Not (nf,fl,pos) -> let nf_norm = normalize_formula nf in CP.Not(nf_norm,fl,pos)
    | CP.Forall (qid, qf,fl,pos) -> let qf_norm = normalize_formula qf in CP.Forall(qid,qf_norm,fl,pos)
    | CP.Exists (qid, qf,fl,pos) -> let qf_norm = normalize_formula qf in CP.Exists(qid,qf_norm,fl,pos))

let rec convert_inf_exp (exp: CP.exp) : CP.exp =
  match exp with
    | CP.Null _
    | CP.IConst _
    | CP.AConst _ -> exp
    | CP.InfConst (i,pos) -> CP.Var(CP.SpecVar(Int,i,Unprimed),pos)
    | CP.Tsconst _
    | CP.FConst _
    | CP.Var _ -> exp
    | CP.Add (a1, a2, pos) -> let a1_conv = convert_inf_exp a1 in
                              let a2_conv = convert_inf_exp a2 in
                              CP.Add(a1_conv,a2_conv,pos)
    | CP.Subtract (a1, a2, pos) -> let a1_conv = convert_inf_exp a1 in
                                   let a2_conv = convert_inf_exp a2 in
                                   CP.Subtract(a1_conv,a2_conv,pos)
    | CP.Mult (a1, a2, pos) -> let a1_conv = convert_inf_exp a1 in
                               let a2_conv = convert_inf_exp a2 in
                               CP.Mult(a1_conv,a2_conv,pos)
    | CP.Div (a1, a2, pos) -> let a1_conv = convert_inf_exp a1 in
                              let a2_conv = convert_inf_exp a2 in
                              CP.Div(a1_conv,a2_conv,pos)
    | CP.Max (a1, a2, pos) -> let a1_conv = convert_inf_exp a1 in
                              let a2_conv = convert_inf_exp a2 in
                              CP.Max(a1_conv,a2_conv,pos)
    | CP.Min (a1, a2, pos) -> let a1_conv = convert_inf_exp a1 in
                              let a2_conv = convert_inf_exp a2 in
                              CP.Min(a1_conv,a2_conv,pos)
    | CP.Bag _
    | CP.BagUnion _
    | CP.BagIntersect _
    | CP.BagDiff _
    | CP.List _
    | CP.ListAppend _
    | CP.ListCons _
    | CP.ListHead _
    | CP.ListTail _
    | CP.ListLength _
    | CP.ListReverse _
    | CP.Func _
    | CP.ArrayAt _ -> exp

let rec convert_inf_b_formula (bf: CP.b_formula) : CP.b_formula =
  let (p_f,bf_ann) = bf in
  let p_f_conv = 
  (match p_f with 
    | CP.XPure _
    | CP.LexVar _
    | CP.BConst _
    | CP.BVar _ -> p_f
    | CP.Lt (e1,e2,pos) -> let e1_conv = convert_inf_exp e1 in
                           let e2_conv = convert_inf_exp e2 in
                           CP.Lt(e1_conv,e2_conv,pos)
    | CP.Lte (e1,e2,pos) -> let e1_conv = convert_inf_exp e1 in
                            let e2_conv = convert_inf_exp e2 in
                            CP.Lte(e1_conv,e2_conv,pos)
    | CP.Gt (e1,e2,pos) -> let e1_conv = convert_inf_exp e1 in
                           let e2_conv = convert_inf_exp e2 in
                           CP.Gt(e1_conv,e2_conv,pos)
    | CP.Gte (e1,e2,pos) -> let e1_conv = convert_inf_exp e1 in
                            let e2_conv = convert_inf_exp e2 in
                            CP.Gte(e1_conv,e2_conv,pos)
    | CP.SubAnn (e1,e2,pos) -> p_f
    | CP.Eq (e1,e2,pos) -> let e1_conv = convert_inf_exp e1 in
                           let e2_conv = convert_inf_exp e2 in
                           CP.Eq(e1_conv,e2_conv,pos)
    | CP.Neq (e1,e2,pos) -> let e1_conv = convert_inf_exp e1 in
                            let e2_conv = convert_inf_exp e2 in
                            CP.Neq(e1_conv,e2_conv,pos)
    | CP.ListIn (e1,e2,pos)
    | CP.ListNotIn (e1,e2,pos)
    | CP.ListAllN (e1,e2,pos)
    | CP.ListPerm (e1,e2,pos) -> p_f
    | CP.EqMax (e1,e2,e3,pos) -> let e1_conv = convert_inf_exp e1 in
                                 let e2_conv = convert_inf_exp e2 in
                                 let e3_conv = convert_inf_exp e3 in
                                 CP.EqMax(e1_conv,e2_conv,e3_conv,pos)
    | CP.EqMin (e1,e2,e3,pos) -> let e1_conv = convert_inf_exp e1 in
                                 let e2_conv = convert_inf_exp e2 in
                                 let e3_conv = convert_inf_exp e3 in
                                 CP.EqMin(e1_conv,e2_conv,e3_conv,pos)
    | CP.BagIn _
    | CP.BagNotIn _
    | CP.BagSub _
    | CP.BagMin _
    | CP.BagMax _
    | CP.VarPerm _
    | CP.RelForm _ -> p_f
  ) in (p_f_conv,bf_ann)

let rec convert_inf_to_var (pf:CP.formula) : CP.formula =
  match pf with
    | CP.BForm (b,fl) -> let b_norm = convert_inf_b_formula b in CP.BForm(b_norm,fl) 
    | CP.And (pf1,pf2,pos) -> let pf1_norm = convert_inf_to_var pf1 in
                              let pf2_norm = convert_inf_to_var pf2 in
                              CP.And(pf1_norm,pf2_norm,pos) 
    | CP.AndList pflst -> let pflst_norm = List.map 
                            (fun (sl,pf) -> (sl,convert_inf_to_var pf)) pflst in CP.AndList(pflst_norm)
    | CP.Or (pf1,pf2,fl,pos) -> let pf1_norm = convert_inf_to_var pf1 in
                                let pf2_norm = convert_inf_to_var pf2 in
                                CP.Or(pf1_norm,pf2_norm,fl,pos) 
    | CP.Not (nf,fl,pos) -> let nf_norm = convert_inf_to_var nf in CP.Not(nf_norm,fl,pos)
    | CP.Forall (qid, qf,fl,pos) -> let qf_norm = convert_inf_to_var qf in CP.Forall(qid,qf_norm,fl,pos)
    | CP.Exists (qid, qf,fl,pos) -> let qf_norm = convert_inf_to_var qf in CP.Exists(qid,qf_norm,fl,pos)


let rec contains_inf_eq_b_formula (bf: CP.b_formula) : bool = 
 let (p_f,bf_ann) = bf in
  match p_f with 
    | CP.XPure _
    | CP.LexVar _
    | CP.BConst _
    | CP.BVar _ -> false
    | CP.Lt (e1,e2,pos) 
    | CP.Lte (e1,e2,pos)
    | CP.Gt (e1,e2,pos)
    | CP.Gte (e1,e2,pos) -> false
    | CP.Eq (e1,e2,pos) -> if CP.is_inf e1 || CP.is_inf e2 then true else false
    | CP.Neq (e1,e2,pos) -> false
    | CP.SubAnn (e1,e2,pos) 
    | CP.ListIn (e1,e2,pos)
    | CP.ListNotIn (e1,e2,pos)
    | CP.ListAllN (e1,e2,pos)
    | CP.ListPerm (e1,e2,pos) -> false
    | CP.EqMax (e1,e2,e3,pos) 
    | CP.EqMin (e1,e2,e3,pos) -> false
    | CP.BagIn _
    | CP.BagNotIn _
    | CP.BagSub _
    | CP.BagMin _
    | CP.BagMax _
    | CP.VarPerm _
    | CP.RelForm _ -> false

let rec contains_inf_eq (pf:CP.formula) : bool =
  match pf with
    | CP.BForm (b,fl) -> contains_inf_eq_b_formula b 
    | CP.And (pf1,pf2,pos) -> contains_inf_eq pf1 || contains_inf_eq pf2
    | CP.AndList pflst -> List.exists 
                            (fun (sl,pf) -> contains_inf_eq pf) pflst
    | CP.Or (pf1,pf2,fl,pos) -> contains_inf_eq pf1 || contains_inf_eq pf2
    | CP.Not (nf,fl,pos) -> contains_inf_eq nf
    | CP.Forall (qid, qf,fl,pos) 
    | CP.Exists (qid, qf,fl,pos) -> contains_inf_eq qf
 
let normalize_inf_formula (f: CP.formula): CP.formula = 
  (*let pf = MCP.pure_of_mix f in*)
  let pf_norm = normalize_formula f in 
  (*if contains_inf_eq f then 
  let f = (*MCP.mix_of_pure*) (convert_inf_to_var pf_norm) in 
  let x_sv = CP.SpecVar(Int,"x",Unprimed) in
  let x_var =  CP.Var(x_sv,no_pos) in
  let inf_var =  CP.Var(CP.SpecVar(Int,"ZInfinity",Unprimed),no_pos) in (* Same Name as in parser.ml *)
  let x_f = CP.BForm((CP.Lte(x_var,inf_var,no_pos),None),None) in
  let inf_constr = CP.Forall(x_sv,x_f,None,no_pos) in
  let f = CP.And(f,inf_constr,no_pos) in f
  else*) let f = (*MCP.mix_of_pure*) (convert_inf_to_var pf_norm) in f
  (*let _ = DD.vv_trace("Normalized: "^ (string_of_pure_formula pf_norm)) in*)
  

let normalize_inf_formula (f: CP.formula): CP.formula =
  let pr = string_of_pure_formula in
  DD.ho_1 "normalize_inf_formula" pr pr normalize_inf_formula f
