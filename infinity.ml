(* Created on 20th Dec 2012 by asankhs to handle Infinity *)

open Globals
open Gen
open Cprinter

module CP = Cpure
module MCP = Mcpure
module DD = Debug
open CP


(* Equisatisfiable Normalization *)
(* 
   v<=\inf      ==> true
   v>=\inf      ==> v=\inf
   v<=-\inf     ==> v=-\inf
   v>=-\inf     ==> true
   min(w,\inf)  ==> w
   min(w,-\inf) ==> -\inf
   max(w,\inf)  ==> \inf
   max(w,-\inf) ==> w
   v<inf        ==> not(v=inf)
   v>inf        ==> false
   v<-inf       ==> false
   v>-inf       ==> not(v=-inf)
   \inf!=c      ==> true
   \inf=c       ==> false
   \inf<=c      ==> false
   \inf>c       ==> true
*)


(*
Normalizes Min and Max Exp as per the rules
   min(w,\inf)  ==> w
   min(w,-\inf) ==> -\inf
   max(w,\inf)  ==> \inf
   max(w,-\inf) ==> w
*)
let rec normalize_exp (exp: CP.exp) : CP.exp =
  let _ = DD.vv_trace("in normalize_exp: "^ (string_of_formula_exp exp)) in
  match exp with
    | CP.Min(e1,e2,pos) -> 
          let e1_norm = normalize_exp e1 in
          let e2_norm = normalize_exp e2 in
          if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then e1_norm
          else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then e2_norm
          else CP.Min(e1_norm,e2_norm,pos)
    | CP.Max(e1,e2,pos) -> 
          let e1_norm = normalize_exp e1 in
          let e2_norm = normalize_exp e2 in
          if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then e2_norm
          else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then e1_norm
          else CP.Max(e1_norm,e2_norm,pos)
            (*| CP.Add(e1,e2,pos) -> let e1_norm = normalize_exp e1 in
    		  let e2_norm = normalize_exp e2 in
    		  if CP.is_const_or_var e1_norm && CP.is_inf e2_norm
    		  then e2_norm
    		  else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm
    		  then e1_norm
    		  else CP.Add(e1_norm,e2_norm,pos)*)                          
    | _ -> exp

(*
--eps converts v>w to 1+w <= v detect it and revert back to substitute \inf during normalization
*)
let check_leq (exp1: CP.exp) (exp2: CP.exp) pos : CP.p_formula = 
  match exp1,exp2 with
    | CP.Add(e1,e2,_),CP.Var(sv,_) -> 
          if is_one e1 && is_var e2 then Gt(exp2,e2,pos)
          else if is_var e1 && is_one e2 then Gt(exp2,e1,pos)
          else Lte(exp1,exp2,pos)
    | _ -> Lte(exp1,exp2,pos)
(* 
Returns true if both side of exp1 is \inf 
used to handle rules with infinity in both sides
   \inf+\inf=0   ==> false
     // \inf=-\inf  ==> false
   \inf+c+\inf=0 ==> ?false
     // \inf+c=-\inf  ==> ?false?
*)

let check_neg_inf2_inf (exp1: CP.exp) (exp2: CP.exp) : bool = 
  match exp1 with
    | CP.Add(e1,e2,pos) ->
          (* WN : why dos e1,e2 need to be both \inf? *)
          if CP.is_inf e1 && CP.is_inf e2
    	  then
            if CP.is_int exp2
    	    then
              (match exp2 with
    		    | CP.IConst(b,_) -> if b == 0 then true else false
    		    | _ -> false)
    	    else false
    	  else false
    | _ -> false

(*
Return true if exp1 is \inf and exp2 is const
used to detect c = -\inf as c + \inf = 0 
*)
let check_neg_inf2_const (exp1: CP.exp) (exp2: CP.exp) : bool = 
  match exp1 with
    | CP.Add(e1,e2,pos) -> 
          if (CP.is_inf e1 && CP.is_const_exp e2) || (CP.is_inf e2 && CP.is_const_exp e1)
    	  then 
            if CP.is_int exp2
    	    then (match exp2 with
    		  | CP.IConst(b,_) -> if b == 0 then true else false
    		  | _ -> false)
    	    else false
    	  else false
    | _ -> false

(*
Return true if exp1 is \inf or exp2 is \inf
used to detect v = -\inf as v + \inf = 0 
*)

let check_neg_inf2 (exp1: CP.exp) (exp2: CP.exp) : bool = 
  match exp1 with
    | CP.Add(e1,e2,pos) -> 
          if CP.is_inf e1 || CP.is_inf e2 
    	  then
            if CP.is_int exp2
    	    then (match exp2 with
    		  | CP.IConst(b,_) -> if b == 0 then true else false
    		  | _ -> false)
    	    else false
    	  else false
    | _ -> false

(*
Same as check_neg_inf2 but with 3 exps used for EqMax and EqMin
*)
let check_neg_inf (exp1: CP.exp) (exp2: CP.exp) (exp3: CP.exp) 
      : bool * CP.exp * CP.exp = 
  match exp1 with
    | CP.Add(a1,a2,pos) -> 
          let oexp = 
            if CP.is_inf a1 then a2 
            else 
 			  if CP.is_inf a2 then a1 else exp1 
          in
  	      (match exp2 with
    	    | CP.Add(e1,e2,pos) -> 
                  let flag = 
                    if CP.is_inf e1 || CP.is_inf e2 
    			    then
                      if CP.is_int exp3
    			      then (match exp3 with
    			   	    | CP.IConst(b,_) -> if b == 0 then true else false
    			   	    | _ -> false)
    			      else false
    			    else false
    			  in let exp = 
                    if CP.is_inf e1 then e2 
                    else 
    			   	  if CP.is_inf e2 then e2 else exp2
    			  in flag,oexp,exp
    	    | _ -> match exp3 with
    	     	| CP.Add(e1,e2,pos) -> 
                      let flag = 
                        if CP.is_inf e1 || CP.is_inf e2 
    			   	    then
                          if CP.is_int exp2
      			          then (match exp2 with
				   	        | CP.IConst(b,_) -> 
                                  if b == 0 then true else false
    				   	    | _ -> false)
    				      else false
    				    else false
    				  in let exp = 
                        if CP.is_inf e1 then e1 
                        else 
    			   	      if CP.is_inf e2 then e2 else exp3
    			  	  in flag,oexp,exp
    	     	| _ -> false,exp2,exp3)
    | _ -> false,exp2,exp3

(*
Normalize b_formula containing \inf 
*)

let rec normalize_b_formula (bf: CP.b_formula) :CP.b_formula = 
  let _ = DD.vv_trace("in normalize_b_formula: "^ (string_of_b_formula bf)) in
  let (p_f,bf_ann) = bf in
  let p_f_norm = 
    (match p_f with
      | CP.Lt(e1,e2,pos) -> 
            let e1_norm = normalize_exp e1 in
            let e2_norm = normalize_exp e2 in
            if check_neg_inf2_inf e1_norm e2_norm then CP.BConst(false,pos)
            else if check_neg_inf2_inf e2_norm e1_norm then CP.BConst(true,pos)
            else if check_neg_inf2_const e2_norm e1_norm then CP.BConst(true,pos)
            else if CP.is_const_exp e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos)
            else if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then CP.Neq(e1_norm,e2_norm,pos)
            else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then CP.BConst(false,pos)
            else if check_neg_inf2 e1_norm e2_norm then CP.BConst(false,pos)
            else if check_neg_inf2 e2_norm e1_norm then CP.Neq(e1_norm,e2_norm,pos)
            else CP.Lt(e1_norm,e2_norm,pos)
      | CP.Lte(e1,e2,pos) -> 
            let e1_norm = normalize_exp e1 in
            let e2_norm = normalize_exp e2 in
            if check_neg_inf2_inf e1_norm e2_norm then CP.BConst(false,pos)
            else if check_neg_inf2_inf e2_norm e1_norm then CP.BConst(true,pos)
            else if check_neg_inf2_const e1_norm e2_norm then CP.BConst(false,pos)
            else if CP.is_inf e1_norm && CP.is_const_exp e2_norm then CP.BConst(false,pos)
            else if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos)
            else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then CP.Eq(e1_norm,e2_norm,pos)
            else if check_neg_inf2 e1_norm e2_norm then CP.Eq(e1_norm,e2_norm,pos)
            else if check_neg_inf2 e2_norm e1_norm then CP.BConst(true,pos)
            else check_leq e1_norm e2_norm pos (*CP.Lte(e1_norm,e2_norm,pos)*)
      | CP.Gt(e1,e2,pos) -> 
            let e1_norm = normalize_exp e1 in
            let e2_norm = normalize_exp e2 in
            if check_neg_inf2_inf e1_norm e2_norm then CP.BConst(true,pos)
            else if check_neg_inf2_inf e2_norm e1_norm then CP.BConst(false,pos)
            else if check_neg_inf2_const e1_norm e2_norm then CP.BConst(true,pos)
            else if CP.is_inf e1_norm && CP.is_const_exp e2_norm then CP.BConst(true,pos)
            else if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then CP.BConst(false,pos)
            else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then CP.Neq(e1_norm,e2_norm,pos)
            else if check_neg_inf2 e1_norm e2_norm then CP.Neq(e1_norm,e2_norm,pos)
            else if check_neg_inf2 e2_norm e1_norm then CP.BConst(false,pos)
            else CP.Gt(e1_norm,e2_norm,pos)
      | CP.Gte(e1,e2,pos) -> 
            let e1_norm = normalize_exp e1 in
            let e2_norm = normalize_exp e2 in
            if check_neg_inf2_inf e1_norm e2_norm then CP.BConst(true,pos)
            else if check_neg_inf2_inf e2_norm e1_norm then CP.BConst(false,pos)
            else if CP.is_inf e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos) else
              if check_neg_inf2_const e2_norm e1_norm then CP.BConst(false,pos)
              else if CP.is_const_exp e1_norm && CP.is_inf e2_norm then CP.BConst(false,pos)
              else if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then CP.Eq(e1_norm,e2_norm,pos)
              else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then CP.BConst(true,pos)
              else if check_neg_inf2 e1_norm e2_norm then CP.BConst(true,pos)
              else if check_neg_inf2 e2_norm e1_norm then CP.Eq(e1_norm,e2_norm,pos)
              else CP.Gte(e1_norm,e2_norm,pos)
      | CP.Eq (e1,e2,pos) -> 
            let e1_norm = normalize_exp e1 in
            let e2_norm = normalize_exp e2 in
            if check_neg_inf2_inf e1_norm e2_norm || check_neg_inf2_inf e2_norm e1_norm then CP.BConst(false,pos)
            else if CP.is_inf e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos)
            else if CP.is_const_exp e1_norm && CP.is_inf e2_norm then CP.BConst(false,pos)
            else if CP.is_inf e1_norm && CP.is_const_exp e2_norm then CP.BConst(false,pos)
            else if check_neg_inf2_const e1_norm e2_norm || check_neg_inf2_const e2_norm e1_norm then CP.BConst(false,pos)
            else CP.Eq(e1_norm,e2_norm,pos)
      | CP.Neq (e1,e2,pos) -> 
            let e1_norm = normalize_exp e1 in
            let e2_norm = normalize_exp e2 in
            if check_neg_inf2_inf e1_norm e2_norm || check_neg_inf2_inf e2_norm e1_norm then CP.BConst(true,pos)
            else if CP.is_inf e1_norm && CP.is_inf e2_norm then CP.BConst(false,pos)
            else if CP.is_const_exp e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos)
            else if CP.is_inf e1_norm && CP.is_const_exp e2_norm then CP.BConst(true,pos)
            else if check_neg_inf2_const e1_norm e2_norm || check_neg_inf2_const e2_norm e1_norm
            then CP.BConst(true,pos)
            else CP.Neq(e1_norm,e2_norm,pos)                            
      | CP.EqMax (e1,e2,e3,pos) -> 
            let flag,w1,w2 = check_neg_inf e1 e2 e3 in
			if flag then CP.Eq(w1,w2,pos)
			else
			  let e1_norm = normalize_exp e1 in
              let e2_norm = normalize_exp e2 in
              let e3_norm = normalize_exp e3 in
              if CP.is_const_or_var e2_norm && CP.is_inf e3_norm then CP.Eq(e1_norm,e3_norm,pos)
              else if CP.is_inf e2_norm && CP.is_const_or_var e3_norm then CP.Eq(e1_norm,e2_norm,pos)
              else CP.EqMax(e1_norm,e2_norm,e3_norm,pos)
      | CP.EqMin (e1,e2,e3,pos) -> 
            let flag,w1,w2 = check_neg_inf e1 e2 e3 in
			if flag then CP.Eq(e1,(CP.mkIConst 0 pos),pos)
			else 
			  let e1_norm = normalize_exp e1 in   
              let e2_norm = normalize_exp e2 in
              let e3_norm = normalize_exp e3 in
              if CP.is_const_or_var e2_norm && CP.is_inf e3_norm then CP.Eq(e1_norm,e2_norm,pos)
              else if CP.is_inf e2_norm && CP.is_const_or_var e3_norm then CP.Eq(e1_norm,e3_norm,pos)
              else CP.EqMin(e1_norm,e2_norm,e3_norm,pos)
      | _ -> p_f
    ) in  let _ = DD.vv_trace("in normalized_b_formula: "^ (string_of_b_formula (p_f_norm,bf_ann))) in
    (p_f_norm,bf_ann)

(* 
Main func normalization starts here
*)
let rec normalize_formula (pf: CP.formula) : CP.formula = 
  let _ = DD.vv_trace("in normalize_formula: "^ (string_of_pure_formula pf)) in
  (match pf with 
    | CP.BForm (b,fl) -> 
          let b_norm = normalize_b_formula b in CP.BForm(b_norm,fl) 
    | CP.And (pf1,pf2,pos) -> 
          let pf1_norm = normalize_formula pf1 in
          let pf2_norm = normalize_formula pf2 in
          CP.And(pf1_norm,pf2_norm,pos) 
    | CP.AndList pflst -> 
          let pflst_norm = List.map 
            (fun (sl,pf) -> (sl,normalize_formula pf)) pflst in CP.AndList(pflst_norm)
    | CP.Or (pf1,pf2,fl,pos) -> 
          let pf1_norm = normalize_formula pf1 in
          let pf2_norm = normalize_formula pf2 in
          CP.Or(pf1_norm,pf2_norm,fl,pos) 
    | CP.Not (nf,fl,pos) -> 
          let nf_norm = normalize_formula nf in CP.Not(nf_norm,fl,pos)
    | CP.Forall (qid, qf,fl,pos) -> 
          let qf_norm = normalize_formula qf in CP.Forall(qid,qf_norm,fl,pos)
    | CP.Exists (qid, qf,fl,pos) -> 
          let qf_norm = normalize_formula qf in CP.Exists(qid,qf_norm,fl,pos))

let convert_inf_to_var (pf:CP.formula) : CP.formula =
  let f_f f = None in
  let f_bf bf = None in
  let f_e e = 
    match e with
      | InfConst (i,pos) -> Some (CP.Var(CP.SpecVar(Int,i,Unprimed),pos))
      | _ -> None
  in
  map_formula pf (f_f,f_bf,f_e)

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
    | CP.Eq (e1,e2,pos) -> if CP.is_inf e1 || CP.is_inf e2 || check_neg_inf2 e1 e2 || check_neg_inf2 e2 e1 
      then  true else false
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
    
(*
Check if the formula contains any assignment to \inf
*)
let rec contains_inf_eq (pf:CP.formula) : bool  =
  match pf with
    | CP.BForm (b,fl) -> contains_inf_eq_b_formula b 
    | CP.And (pf1,pf2,pos) -> contains_inf_eq pf1 || contains_inf_eq pf2
    | CP.AndList pflst -> List.exists 
                            (fun (sl,pf) -> contains_inf_eq pf) pflst
    | CP.Or (pf1,pf2,fl,pos) -> contains_inf_eq pf1 || contains_inf_eq pf2
    | CP.Not (nf,fl,pos) -> contains_inf_eq nf
    | CP.Forall (qid, qf,fl,pos) 
    | CP.Exists (qid, qf,fl,pos) -> contains_inf_eq qf

module EM = Gen.EqMap(CP.SV)


(*
Find the substitutions with \inf 
 
   x=\inf & x=c \/ x+\inf=0 & x=c
   ==> [(x=\inf & x=c,[x->\inf,x->c]),
        (x+\inf=0 & x=c,[x->-\inf,x->c])
       ]
*)
let find_inf_subs (f:CP.formula) : (CP.formula * EM.emap) list =
  let ds = CP.split_disjunctions f in
  let find_inf_eq e =
    let f_f f = 
    	(match f with
    	| And _ | AndList _  | BForm _ -> None 
    	| _ -> Some [])
    in
    let f_bf bf = 
      (match bf with
        | ((Eq _) as e),_ -> Some ([bf]) 
        | _,_ -> Some ([])
      )
    in
    let f_e e = Some ([]) in
    (* let f_arg = (fun _ _ -> ()),(fun _ _ -> ()),(fun _ _ -> ()) in *)
    (* let subs e = trans_formula e () (f_f,f_bf,f_e) f_arg List.concat in *)
    let find_eq e = fold_formula e (f_f,f_bf,f_e) List.concat in
    let pr = string_of_pure_formula in
    let prl l = pr_list string_of_b_formula l in
    let find_eq e = DD.no_1 "find_inf_subs" pr prl find_eq e in
    let eq_list = find_eq e in
    let eq_list_vars = List.filter (fun bf ->  let (p_f,bf_ann) = bf in
    					match p_f with
  					| Eq(e1,e2,pos) -> if is_var e1 && is_var e2 then true else false
    					| _ -> false
    			) eq_list in
    let eqset = EM.mkEmpty in
    let neg_inf = CP.SpecVar(Int,constinfinity,Primed) in
    let eqset = List.fold_left (fun eset exp -> 
			        let (p_f,bf_ann) = exp in
    				(match p_f with
    				| Eq (e1,e2,pos) -> (match e1,e2 with
    						    | Var(sv1,_),Var(sv2,_) -> EM.add_equiv eset sv1 sv2
                                | _,IConst(0,_) -> 
                                    (match e1 with 
                                       | Add(a1,a2,_) -> 
                                           (match a1, a2 with 
                                           | Var(sa1,_),Var(sa2,_) -> if is_inf a1 
                                                          then EM.add_equiv eset sa2 neg_inf
                                             else if is_inf a2 then EM.add_equiv eset sa1 neg_inf
                                             else eset
                                           | _ -> eset)
                                       | _ -> eset)
             			        | _ -> eset)
    				| _ -> eset)
    				) eqset eq_list in eqset 
  in 
  List.map (fun e -> (e,find_inf_eq e)) ds

let rec sub_inf_list_exp (exp: CP.exp) (vars: CP.spec_var list) (is_neg: bool) : CP.exp =
  match exp with
    | CP.Null _
    | CP.IConst _
    | CP.AConst _ 
    | CP.InfConst _
    | CP.Tsconst _
    | CP.FConst _ -> exp
    | CP.Var (sv,pos) -> 
        if BList.mem_eq eq_spec_var sv vars 
        then if is_neg then (mkSubtract (IConst(0,pos)) (Var(SpecVar(Int,constinfinity,Unprimed),pos)) pos)
          else CP.Var(CP.SpecVar(Int,constinfinity,Unprimed),pos) 
        else exp
    | CP.Add (a1, a2, pos) -> 
          let a1_conv = sub_inf_list_exp a1 vars is_neg in
          let a2_conv = sub_inf_list_exp a2 vars is_neg in
          CP.Add(a1_conv,a2_conv,pos)
    | CP.Subtract (a1, a2, pos) -> 
          let a1_conv = sub_inf_list_exp a1 vars is_neg in
          let a2_conv = sub_inf_list_exp a2 vars is_neg in
          CP.Subtract(a1_conv,a2_conv,pos)
    | CP.Mult (a1, a2, pos) -> 
          let a1_conv = sub_inf_list_exp a1 vars is_neg in
          let a2_conv = sub_inf_list_exp a2 vars is_neg in
          CP.Mult(a1_conv,a2_conv,pos)
    | CP.Div (a1, a2, pos) -> 
          let a1_conv = sub_inf_list_exp a1 vars is_neg in
          let a2_conv = sub_inf_list_exp a2 vars is_neg in
          CP.Div(a1_conv,a2_conv,pos)
    | CP.Max (a1, a2, pos) -> 
          let a1_conv = sub_inf_list_exp a1 vars is_neg in
          let a2_conv = sub_inf_list_exp a2 vars is_neg in
          CP.Max(a1_conv,a2_conv,pos)
    | CP.Min (a1, a2, pos) -> 
          let a1_conv = sub_inf_list_exp a1 vars is_neg in
          let a2_conv = sub_inf_list_exp a2 vars is_neg in
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
    
let rec sub_inf_list_b_formula (bf:CP.b_formula) (vl: CP.spec_var list) (is_neg: bool) : CP.b_formula = 
  let (p_f,bf_ann) = bf in
  let p_f_conv = 
    (match p_f with 
      | CP.XPure _
      | CP.LexVar _
      | CP.BConst _
      | CP.BVar _ -> p_f
      | CP.Lt (e1,e2,pos) -> 
            let e1_conv = sub_inf_list_exp e1 vl is_neg in
            let e2_conv = sub_inf_list_exp e2 vl is_neg in
            CP.Lt(e1_conv,e2_conv,pos)
      | CP.Lte (e1,e2,pos) -> 
            let e1_conv = sub_inf_list_exp e1 vl is_neg in
            let e2_conv = sub_inf_list_exp e2 vl is_neg in
            CP.Lte(e1_conv,e2_conv,pos)
      | CP.Gt (e1,e2,pos) -> 
            let e1_conv = sub_inf_list_exp e1 vl is_neg in
            let e2_conv = sub_inf_list_exp e2 vl is_neg in
            CP.Gt(e1_conv,e2_conv,pos)
      | CP.Gte (e1,e2,pos) -> 
            let e1_conv = sub_inf_list_exp e1 vl is_neg in
            let e2_conv = sub_inf_list_exp e2 vl is_neg in
            CP.Gte(e1_conv,e2_conv,pos)
      | CP.SubAnn (e1,e2,pos) -> p_f
      | CP.Eq (e1,e2,pos) -> 
      	    if (is_var e1 && is_inf e2) || (is_var e2 && is_inf e1) 
              || (check_neg_inf2 e1 e2) || (check_neg_inf2 e2 e1)
            then p_f else
            let e1_conv = sub_inf_list_exp e1 vl is_neg in
            let e2_conv = sub_inf_list_exp e2 vl is_neg in
            CP.Eq(e1_conv,e2_conv,pos)
      | CP.Neq (e1,e2,pos) -> 
            let e1_conv = sub_inf_list_exp e1 vl is_neg in
            let e2_conv = sub_inf_list_exp e2 vl is_neg in
            CP.Neq(e1_conv,e2_conv,pos)
      | CP.ListIn (e1,e2,pos)
      | CP.ListNotIn (e1,e2,pos)
      | CP.ListAllN (e1,e2,pos)
      | CP.ListPerm (e1,e2,pos) -> p_f
      | CP.EqMax (e1,e2,e3,pos) -> 
            let e1_conv = sub_inf_list_exp e1 vl is_neg in
            let e2_conv = sub_inf_list_exp e2 vl is_neg in
            let e3_conv = sub_inf_list_exp e3 vl is_neg in
            CP.EqMax(e1_conv,e2_conv,e3_conv,pos)
      | CP.EqMin (e1,e2,e3,pos) -> 
            let e1_conv = sub_inf_list_exp e1 vl is_neg in
            let e2_conv = sub_inf_list_exp e2 vl is_neg in
            let e3_conv = sub_inf_list_exp e3 vl is_neg in
            CP.EqMin(e1_conv,e2_conv,e3_conv,pos)
      | CP.BagIn _
      | CP.BagNotIn _
      | CP.BagSub _
      | CP.BagMin _
      | CP.BagMax _
      | CP.VarPerm _
      | CP.RelForm _ -> p_f
    ) in (p_f_conv,bf_ann)
    
(*
substitute all variables in vl with \inf in f
*)
let rec sub_inf_list (f:CP.formula) (vl: CP.spec_var list) (is_neg: bool) : CP.formula = 
  let rec helper pf vl =
    match pf with
      | CP.BForm (b,fl) -> 
            let b_norm = sub_inf_list_b_formula b vl is_neg
            in CP.BForm(b_norm,fl) 
      | CP.And (pf1,pf2,pos) -> 
            let pf1_norm = helper pf1 vl in
            let pf2_norm = helper pf2 vl in
            CP.And(pf1_norm,pf2_norm,pos) 
      | CP.AndList pflst -> 
            let pflst_norm = List.map (fun (sl,pf) -> (sl,helper pf vl)) pflst 
            in CP.AndList(pflst_norm)
      | CP.Or (pf1,pf2,fl,pos) -> 
            let pf1_norm = helper pf1 vl in
            let pf2_norm = helper pf2 vl in
            CP.Or(pf1_norm,pf2_norm,fl,pos) 
      | CP.Not (nf,fl,pos) -> 
            let nf_norm = helper nf vl
            in CP.Not(nf_norm,fl,pos)
      | CP.Forall (qid, qf,fl,pos) -> 
            let qf_norm = helper qf vl
            in CP.Forall(qid,qf_norm,fl,pos)
      | CP.Exists (qid, qf,fl,pos) -> 
            let qf_norm = helper qf vl
            in CP.Exists(qid,qf_norm,fl,pos)
  in
  helper f vl
  
(*
do the substitutions with \inf 
*)
let find_equiv_all_x  (e:EM.elem) (s:EM.emap) : EM.elist  =
    let pr = EM.string_of_elem in
    let pr2 = pr_list EM.string_of_elem in 
    Debug.no_1 "find_equiv_all" pr pr2 (fun _ -> EM.find_equiv_all e s) e
    
let substitute_inf (f: CP.formula) : CP.formula =
  let f = convert_inf_to_var f in
  let sublist = find_inf_subs f in
  let after_sub = List.map (fun (pf,kv) -> 
  			(*let filter_infs = List.filter (fun (e,k) -> is_inf_sv k) kv in
  			let vlistlist = List.map (fun (e,k) -> EM.find_equiv_all e kv) filter_infs in
                        let vlist = List.flatten vlistlist in*)
                        let svlist = (find_equiv_all_x (SpecVar(Int,constinfinity,Unprimed)) kv) in  	
  			            let new_pf = sub_inf_list pf svlist false in
                        let svneglist = (find_equiv_all_x (SpecVar(Int,constinfinity,Primed)) kv) in  
	                    let new_pf = sub_inf_list new_pf svneglist true in
                        arith_simplify 10 new_pf) sublist in 
  join_disjunctions after_sub

let rec normalize_inf_formula_sat (f: CP.formula): CP.formula = 
  (*let pf = MCP.pure_of_mix f in*)
  let pf_norm = normalize_formula f in 
  if contains_inf_eq pf_norm then 
    let fs = substitute_inf pf_norm in
    normalize_formula fs
        (*let f = (*MCP.mix_of_pure*) (convert_inf_to_var pf_norm) in 
          let x_sv = CP.SpecVar(Int,"x",Unprimed) in
          let x_var =  CP.Var(x_sv,no_pos) in
          let inf_var =  CP.Var(CP.SpecVar(Int,"ZInfinity",Unprimed),no_pos) in (* Same Name as in parser.ml *)
          let x_f = CP.BForm((CP.Lte(x_var,inf_var,no_pos),None),None) in
          let inf_constr = CP.Forall(x_sv,x_f,None,no_pos) in
          let f = CP.And(f,inf_constr,no_pos) in f*)
  else let f = (*MCP.mix_of_pure*) (convert_inf_to_var pf_norm) in f
  (*let _ = DD.vv_trace("Normalized: "^ (string_of_pure_formula pf_norm)) in*)
  

let normalize_formula (f: CP.formula): CP.formula =
  let pr = string_of_pure_formula in
  DD.no_1 "normalize_formula" pr pr normalize_formula f
  
let normalize_inf_formula_imply (ante: CP.formula) (conseq: CP.formula) : CP.formula * CP.formula = 
  let ante_norm = normalize_formula ante in
  let conseq_norm = normalize_formula conseq in 
  let new_c = if contains_inf_eq conseq_norm 
  		then normalize_formula (substitute_inf conseq_norm) 
  		else convert_inf_to_var conseq_norm in
  let new_a = if contains_inf_eq ante_norm 
  		then normalize_formula (substitute_inf ante_norm)
  		else convert_inf_to_var ante_norm in
  let atoc_sublist = find_inf_subs new_a in
  if List.length atoc_sublist == 1 
  then let _,subs_c = List.hd atoc_sublist in 
  	let vlist = find_equiv_all_x (SpecVar(Int,constinfinity,Unprimed)) subs_c in
  	let new_c = sub_inf_list new_c vlist false in (* substitute +ve inf *)
    let negvlist =  find_equiv_all_x (SpecVar(Int,constinfinity,Primed)) subs_c in
    let new_c =  sub_inf_list new_c negvlist true in (* substitute -ve inf *)
    let new_c = arith_simplify 11 new_c in
  	new_a,(normalize_formula new_c)
  else new_a,new_c
