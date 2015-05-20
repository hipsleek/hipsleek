#include "xdebug.cppo"
open Globals
open VarGen

open Error
open Cpure
type var_rep = string

type sformula = 
  | STrue
  | SFalse
  | SComp of scform

and scform = 
  | Seq of (var_rep*var_rep)
  | Sneq of (var_rep*var_rep)
  | SAnd of (scform * scform)
  | SOr of (scform * scform)

let rec string_of_scformula f = match f with 
  | Seq (v1,v2) -> v1^" = "^v2
  | Sneq (v1,v2) -> v1^" != "^v2
  | SAnd (f1,f2) -> (string_of_scformula f1)^" & " ^ (string_of_scformula f2)
  | SOr (f1,f2) -> " ("^(string_of_scformula f1)^") | (" ^ (string_of_scformula f2)^") "

let string_of_sformula f = match f with 
  | STrue -> "true"
  | SFalse -> "false"
  | SComp f -> string_of_scformula f 

let s_eq (s1:string) (s2:string) :bool= (*eq_spec_var*) s1 = s2

let mkSAnd f1 f2 = match f1 with 
  | STrue -> f2
  | SFalse -> SFalse
  | SComp fc1 -> match f2 with 
    | STrue -> f1
    | SFalse -> SFalse
    | SComp fc2 -> SComp (SAnd (fc1,fc2))

let mkSOr f1 f2 = match f1 with 
  | STrue -> STrue
  | SFalse -> f2
  | SComp fc1 -> match f2 with 
    | STrue -> STrue
    | SFalse -> f1
    | SComp fc2 -> SComp (SOr (fc1,fc2))

let rec scfv f = match f with
  | Seq (v1,v2) 
  | Sneq(v1,v2) -> [v1;v2]
  | SAnd (f1,f2) 
  | SOr (f1,f2) -> (Gen.BList.remove_dups_eq s_eq ((scfv f1)@ (scfv f2))) 

let subst_s (fr, t) o = if s_eq fr o then t else o

let rec subst_cformula s f = match f with 
  | Seq (v1,v2) -> 
    let r1 = subst_s s v1 in
    let r2 = subst_s s v2 in
    if s_eq r1 r2 then STrue else SComp(Seq(r1,r2))
  | Sneq (v1,v2) -> 
    let r1 = subst_s s v1 in
    let r2 = subst_s s v2 in
    if s_eq r1 r2 then SFalse else SComp(Sneq(r1,r2))
  | SAnd (f1,f2) -> mkSAnd (subst_cformula s f1) (subst_cformula s f2)
  | SOr (f1,f2) -> mkSOr (subst_cformula s f1) (subst_cformula s f2)

let subst_formula s f = match f with 
  | SComp fc -> subst_cformula s fc | _ -> f 

let set_add_eq l (v1,v2) = 
  let rec f_rem v l= match l with 
    | [] -> ([v],[])
    | h::t-> 
      if (Gen.BList.mem_eq s_eq v h) then (h,t) 
      else 
        let r1,r2 = f_rem v t in
        (r1,h::r2) in
  let r11,r2 = f_rem v1 l in
  let r12,r2 = f_rem v2 r2 in
  (Gen.BList.remove_dups_eq s_eq (r11@r12))::r2

let get_aset l v = try List.find (Gen.BList.mem_eq s_eq v) l  with | Not_found -> [v]	

let trans_exp e : var_rep = match e with 
  | Var (v1,_) -> Cprinter.string_of_spec_var v1
  | Null _ -> "null"
  | IConst (i,_) -> string_of_int i
  | FConst (f,_) -> string_of_float f
  | _ -> failwith "found unexpected expression1" 

let trans_bf bf = match bf with 
  | BConst (b,_) -> if b then STrue else SFalse
  | Eq (IConst (c1,_),IConst(c2,_),_) -> if (c1=c2) then STrue else SFalse
  | Eq (FConst (c1,_),FConst(c2,_),_) -> if (c1=c2) then STrue else SFalse 
  | Neq (IConst (c1,_),IConst(c2,_),_) -> if (c1=c2) then SFalse else STrue
  | Neq (FConst (c1,_),FConst(c2,_),_) -> if (c1=c2) then SFalse else STrue
  | Eq (e1,e2,_) -> 
    let v1 = trans_exp e1 in
    let v2 = trans_exp e2 in
    if (s_eq v1 v2) then STrue else SComp (Seq (v1,v2))
  | Neq (e1,e2,_) -> 
    let v1 = trans_exp e1 in
    let v2 = trans_exp e2 in
    if (s_eq v1 v2) then SFalse else SComp (Sneq (v1,v2))
  | BVar (v,_) -> STrue (*SComp (Seq (Cprinter.string_of_spec_var v, "true"))		*)
  | _ -> failwith ("found unexpected expression2 :"^(Cprinter.string_of_b_formula (bf,None))) 

let neg f = match f with 
  | STrue -> SFalse
  | SFalse -> STrue
  | SComp fc ->
    let rec helper fc = match fc with
      | Seq f -> Sneq f
      | Sneq f -> Seq f
      | SAnd (f1,f2) -> SOr (helper f1, helper f2)
      | SOr (f1,f2) -> SAnd (helper f1, helper f2) in
    SComp (helper fc)


let elim_ex v f = match f with 
  | STrue -> STrue
  | SFalse -> SFalse
  | SComp fc1 ->
    let rec purge_v f1  = match f1 with 
      | STrue -> STrue
      | SFalse -> SFalse
      | SComp f1-> 
        let rec h f1 = match f1 with 
          | Seq (v1,v2) -> if (s_eq v1 v)|| (s_eq v2 v) then  failwith ("could not elim ex "^v^" in "^(string_of_sformula f)) else SComp f1
          | Sneq (v1,v2)-> if (s_eq v1 v)|| (s_eq v2 v) then STrue else SComp f1
          | SAnd (f1,f2) -> mkSAnd (h f1) (h f2)
          | SOr  (f1,f2) -> mkSOr  (h f1) (h f2) in
        h f1 in
    let rec or_lin f = match f with | SOr (f1,f2) -> (or_lin f1)@(or_lin f2) | _ -> [f] in
    let rec and1_lin f = match f with | SAnd (f1,f2) -> (and1_lin f1)@(and1_lin f2) | _ -> [f] in

    let rec find_eq f = match f with 
      | Seq (v1,v2) -> if s_eq v v1 then [(v1,v2)] else if (s_eq v v2) then [(v2,v1)] else []
      | SAnd (f1,f2) -> 
        let r = find_eq f1 in
        if r=[] then find_eq f2 else r 
      | _ -> [] in
    let llo = List.map or_lin (and1_lin fc1) in
    let rec search opt lacc l = match l with 
      | [] -> (opt,lacc)
      | h::t -> 
        let lfh = List.concat (List.map find_eq h) in
        let lfh = List.length lfh in
        let lh = List.length h in
        if (lh<>lfh) then search opt (h::lacc) t
        else if (lh=1) then 
          match opt with 
          | None -> (Some h,lacc@t)
          | Some s -> (Some h,lacc@(s::t))
        else match opt with 
          | None -> search (Some h) lacc t
          | Some _ -> search opt (h::lacc) t in
    let s,l = search None [] llo in
    match s with 
    | None -> purge_v f
    | Some s -> 
      let f_or f = List.fold_left (fun a c-> SOr(a,c)) (List.hd f) (List.tl f) in
      let ff_or f = List.fold_left (fun a c-> mkSOr a c) (List.hd f) (List.tl f) in
      let f_and f = SComp (List.fold_left (fun a c-> SAnd (a,(f_or c))) (f_or(List.hd l)) (List.tl l)) in
      let fr = if l=[] then STrue else f_and l in
      if (List.length s)=1 then subst_formula (List.hd (find_eq (List.hd s))) fr
      else ff_or (List.map (fun c-> subst_formula (List.hd (find_eq c)) (mkSAnd (SComp c) fr) ) s)


let rec trans_f b f = match f with 
  | BForm ((bf,_),_) -> trans_bf bf
  | AndList _ -> Gen.report_error no_pos "dp.ml: encountered AndList, should have been already handled"
  | And (f1,f2,_) -> mkSAnd (trans_f b f1) (trans_f b f2)
  | Or (f1,f2,_,_) -> mkSOr (trans_f b f1) (trans_f b f2)
  | Not (f,_,_) -> neg (trans_f b f) 
  | Forall _ -> failwith "unexpected forall!"
  | Exists (v,f,_,_) -> if b then elim_ex (Cprinter.string_of_spec_var v) (trans_f b f) else trans_f b f  

let trans_f b f = Gen.Profiling.do_2 "dptransf" trans_f b f
let sat_check f = 
  let rec and_lin f = match f with | SAnd (f1,f2) -> (and_lin f1)@(and_lin f2) | _ -> [f] in
  let contra_test1 eq_s (v1,v2) = Gen.BList.mem_eq s_eq v2 (get_aset eq_s v1) in
  let contra_test eq_s neq_s = List.exists (contra_test1 eq_s) neq_s in
  let rec helper eqs neqs w_l f = match f with 
    | Seq a ->  
      let eqs = set_add_eq eqs a in
      ( match w_l with 
        | [] -> not (contra_test eqs neqs)
        | h::t -> 
          if (List.exists (fun (v1,v2)->(v1,v2)=a || (v2,v1)=a) neqs) then false
          else helper eqs neqs t h)
    | Sneq a -> 
      (match w_l with 
       | [] -> not (contra_test eqs (a::neqs))
       | h::t -> 
         if contra_test1 eqs a then false
         else helper eqs (a::neqs) t h)
    | SAnd _ -> 
      let l1,l2 = List.partition (fun c-> match c with | SOr _ -> true | _ -> false ) (and_lin f) in
      let l = l2@l1 in
      helper eqs neqs ((List.tl l) @ w_l) (List.hd l) 
    | SOr (f1,f2) -> (helper eqs neqs w_l f1) || (helper eqs neqs w_l f2) in
  helper [] [] [] f 

let is_sat f sat_no = 
  let h f = match trans_f false f with 
    | STrue -> true
    | SFalse -> false
    | SComp fc -> sat_check fc in
  (* print_string (" is sat: "^(Cprinter.string_of_pure_formula f)^"\n \n"); flush(stdout);*)
  Gen.Profiling.do_1 "dpsat" h f

let imply_test afc cfc =   
  let rec t_imply e_s n_s cfc = match cfc with 
    | Seq (v1,v2) -> Gen.BList.mem_eq s_eq v2 (get_aset e_s v1)
    | Sneq (v1,v2) -> 
      let sv1 = get_aset e_s v1 in 
      let sv2 = get_aset e_s v2 in 
      List.exists (fun (v1,v2)-> 
          (Gen.BList.mem_eq s_eq v1 sv1 && Gen.BList.mem_eq s_eq v2 sv2) ||
          (Gen.BList.mem_eq s_eq v1 sv2 && Gen.BList.mem_eq s_eq v2 sv1)) n_s
    | SAnd (f1,f2) -> (t_imply e_s n_s f1) && (t_imply e_s n_s f2)
    | SOr (f1,f2) -> (t_imply e_s n_s f1) || (t_imply e_s n_s f2) in

  let rec icollect afc e_s n_l w_l = match afc with 
    | Seq a -> (match w_l with 
        | [] -> t_imply (set_add_eq e_s a) n_l cfc
        | h::t -> icollect h (set_add_eq e_s a) n_l t)
    | Sneq a -> (match w_l with 
        | [] -> t_imply e_s (a::n_l) cfc
        | h::t -> icollect h e_s (a::n_l) t)	
    | SAnd (f1,f2)-> icollect f1 e_s n_l (f2::w_l)
    | SOr (f1,f2) -> (icollect f1 e_s n_l w_l) && (icollect f2 e_s n_l w_l) in
  icollect afc [] [] [] 

let imply ante conseq impl_no _ = 
  let h ante conseq = match trans_f true conseq with
    | SFalse -> false
    | STrue -> true 
    | SComp cfc -> match trans_f false ante with
      | STrue -> false
      | SFalse -> true
      | SComp afc -> imply_test afc cfc in
  Gen.Profiling.do_2 "dpimply" h ante conseq 

(*
let imply ante conseq i f = Gen.Profiling.do_2 "dpimply" Smtsolver.imply ante conseq(* i f*)
let is_sat f sn = Gen.Profiling.do_2 "dpsat" Smtsolver.is_sat f sn
	*)  
let simplify f = (* (x_add Omega.simplify) *) !Cpure.simplify f

let hull f = x_add_1 Omega.hull f	

let pairwisecheck f = x_add_1 Omega.pairwisecheck f

(*let imply ante conseq impl_no _ = match trans_f false ante with
  | SFalse -> true
  | STrue -> (match trans_f true conseq with
     | STrue -> true 
     | _ -> false)
  | SComp afc -> match (trans_f true conseq) with 
     | STrue -> true
     | SFalse -> false (*if not (sat_check afc) then true else false*)
     | SComp cfc -> 
     (*   if not (sat_check afc) then true
        else if (sat_check cfc) then 
     else *)
     imply_test afc cfc *)




(*
and sets = (var_rep list list * Hashtbl.t)

let sets_add_eq ((s1,s2):sets) (v1,v2) = 
    let le,ln = List.partition (fun c-> (Gen.BList.mem_eq s_eq v1 c)||(Gen.BList.mem_eq s_eq v2 c)) s1 in
		let le = Gen.BList.remove_dups_eq s_eq (v1::(v2::(List.concat le))) in
		let s2 = in
    (le::ln,s2)

let sets_add_neq ((s1,s2):sets) (v1,v2) = 
*)

(*	
let get_nset l v = try snd (List.find (fun (c,_)-> s_eq c v) l) with | Not_found -> []
let sets_add_eq (e_s,n_s) (v1,v2) = 
	let rec f_rem v l= match l with 
		| [] -> ([v],[])
		| h::t-> 
			if (Gen.BList.mem_eq s_eq v h) then (h,t) 
			else 
				let r1,r2 = f_rem v t in
				(r1,h::r2) in
	let rec get s l =match l with 
		| [] -> ([],[])
		| (hv,hl)::t -> 
			if s_eq hv s then (hl,t) 
			else 
				let r1,r2 = get s t in
				(r1,(hv,hl)::r2) in
	let r11,r2 = f_rem v1 l in
	let r12,r2 = f_rem v2 r2 in
	let new_es = Gen.BList.remove_dups_eq s_eq (r11@r12) in
	let e_s = new_es::r2 in
	let folder r n_s c = 
		List.fold_left r 
	let n_s = List.fold_left (folder r12) n_s r11 in
	let n_s = List.fold_left (folder r11) n_s r12 in
	(e_s,n_s)

let sets_add_neq (e_s,n_s) (v1,v2) = 
	let get s l =match l with 
		| [] -> ([],[])
		| (hv,hl)::t -> 
			if s_eq hv s then (hl,t) 
			else 
				let r1,r2 = get s t in
				(r1,(hv,hl)::r2) in
	let v1_ns,r2 = get v1 n_s in
	let v2_ns,r2 = get v2 r2 in
	let nv1 = Gen.BList.remove_dups_eq s_eq (List.concat (List.map (get_nset r2) (get_aset e_s v2))@v1_ns) in
	let nv2 = Gen.BList.remove_dups_eq s_eq (List.concat (List.map (get_nset r2) (get_aset e_s v1))@v2_ns) in
	(e_s, (v2,nv2)::((v1,nv1)::r2))
	*)
