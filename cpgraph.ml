#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Exc.GTable

open Cpure


let get_frame_b_form (b: b_formula) =
  let (pf,_) = b in
  match pf with
  | Frm (sv,_) -> [sv]
  | _ -> []

let get_frame_x p0=
  let rec helper p=
    match p with
    | BForm (b,_) -> get_frame_b_form b
    | And (b1,b2,_) -> (helper b1)@(helper b2)
    | AndList b-> List.fold_left (fun ls (_,b1) -> ls@(helper b1)) [] b
    | Or (b1,b2,_,_) -> intersect_svl (helper b1) (helper b2)
    | Not (b,_,_) -> helper b
    | Forall (_,b,_,_)-> 	helper b
    | Exists (q,b,lbl,l)-> helper b
  in
  helper p0

let get_frame p0=
  let pr1= !Cpure.print_formula in
  let pr2 = !print_svl in
  Debug.no_1 "get_frame" pr1 pr2
    (fun _ -> get_frame_x p0) p0

let get_prune_frame_x p0=
  let rec helper p=
    match p with
    | BForm (b,_) -> let svl = get_frame_b_form b in
      if svl = [] then p,[] else
        (mkTrue no_pos, svl)
    | And (p1,p2,pos) -> begin
        let np1, svl1 = (helper p1) in
        let np2, svl2 = (helper p2) in
        let svl = svl1@svl2 in
        match isConstTrue np1,isConstTrue np2 with
        | true,true -> (np1,svl)
        | true,false -> np2,svl
        | _, true -> np1,svl
        | _ -> (mkAnd np1 np2 pos,svl)
      end
    | AndList b-> let ls_and,svl = List.fold_left (fun (ls1,svl0) (sl,b1) ->
        let nb1,svl1 = helper b1 in
        if svl1 = [] then ls1@[(sl,b1)],svl0 else
          ls1,svl0@svl1
      ) ([],[]) b in
      if svl = [] then (mkTrue no_pos, []) else
        AndList ls_and,svl
    | Or (b1,b2,_,_) -> (*intersect_svl (helper b1) (helper b2)*)
      (p,[])
    | Not (b, _,pos) -> let nb,svl = helper b in
      if svl=[] then p,[] else (mkTrue pos, svl)
    | Forall (_,b,_,pos)-> let nb,svl = helper b in
      if svl=[] then p,[] else (mkTrue pos, svl)
    | Exists (q,b,lbl,pos)-> let nb,svl = helper b in
      if svl=[] then p,[] else (mkTrue pos, svl)
  in
  helper p0

let get_prune_frame p0=
  let pr1= !print_formula in
  let pr2 = !print_svl in
  Debug.no_1 "get_prune_frame" pr1 (pr_pair pr1 pr2)
    (fun _ -> get_prune_frame_x p0) p0

let prune_irr_neq_b_form b irr_svl comps=
  let rec test sv1 sv2 comps=
    match comps with
    | [] -> false
    | [x] -> false
    | comp::rest -> begin
        let b1 = mem_svl sv1 comp in
        let b2 = mem_svl sv2 comp in
        match b1,b2 with
        | true,true -> false
        | true,false -> true
        | false,true -> true
        | false,false -> test sv1 sv2 rest
      end
  in
  let (pf,c) = b in
  match pf with
  | Neq (a1, a2, pos)
  | Eq (a1, a2, pos) -> begin
      match a1,a2 with
      | Var (sv1,pos1), Var (sv2,pos2) ->
        if (List.exists (fun sv -> (eq_spec_var sv sv1) || (eq_spec_var sv sv2)) irr_svl) || (test sv1 sv2 comps) then
          (true,  (BConst (true,pos),c))
        else (false,b)
      | _ -> (false,b)
    end
  | _ -> (false,b)

let prune_irr_neq_x p0 irr_svl comps=
  let rec helper p=
    match p with
    | BForm (bf,a) -> let b,nbf = prune_irr_neq_b_form bf irr_svl comps in
      if b then b, mkTrue no_pos else
        false, BForm (nbf,a)
    | And (p1,p2,pos) -> begin
        let b1,np1 = (helper p1) in
        let b2,np2 = (helper p2) in
        match b1,b2 with
        | true,true -> (true, mkTrue no_pos)
        | true,false -> false,np2
        | _, true -> false,np1
        | _ -> (false,mkAnd np1 np2 pos)
      end
    | AndList b-> false,p
    (* let ls_and,svl = List.fold_left (fun (ls1,) (sl,b1) -> *)
    (*     let nb1,svl1 = helper b1 in *)
    (*     if svl1 = [] then ls1@[(sl,b1)],svl0 else *)
    (*       ls1,svl0@svl1 *)
    (* ) ([],[]) b in *)
    (* if svl = [] then (mkTrue no_pos, []) else *)
    (*   AndList ls_and,svl *)
    | Or (b1,b2,_,_) -> (*intersect_svl (helper b1) (helper b2)*)
      false,p
    | Not (b, _,pos) -> let b,np = helper b in
      if b then false,mkFalse no_pos else (false, np)
    | Forall (a,b,c,pos)-> let b,np = helper b in
      if b then b,mkTrue pos else false,Forall (a,np,c,pos)
    | Exists (q,b,lbl,pos)-> let b,np = helper b in
      if b then b,mkTrue pos else (false,Exists (q,np,lbl,pos))
  in
  helper p0

let prune_irr_neq p0 comps=
  let svl = List.concat comps in
  let irr_svl = diff_svl (remove_dups_svl (fv p0)) svl in
  let pr1= !print_formula in
  let pr2 = !print_svl in
  Debug.no_3 "prune_irr_neq" pr1 pr2 (pr_list pr2) (pr_pair string_of_bool pr1)
    (fun _ _ _ -> prune_irr_neq_x p0 irr_svl comps) p0 irr_svl comps



let prune_irr_neq_b_form_ll b irr_svl comps=
  let rec test sv1 sv2 comps=
    match comps with
    | [] -> false
    | [x] -> false
    | comp::rest -> begin
        let b1 = mem_svl sv1 comp in
        let b2 = mem_svl sv2 comp in
        match b1,b2 with
        | true,true -> false
        | true,false -> true
        | false,true -> true
        | false,false -> test sv1 sv2 rest
      end
  in
  let (pf,c) = b in
  match pf with
  | Neq (a1, a2, pos)
  | Eq (a1, a2, pos) -> begin
      match a1,a2 with
      | Var (sv1,pos1), Var (sv2,pos2) ->
        if (List.exists (fun sv -> (eq_spec_var sv sv1) || (eq_spec_var sv sv2)) irr_svl) || (test sv1 sv2 comps) then
          (true,  (BConst (true,pos),c))
        else (false,b)
      | _ -> (false,b)
    end
  | _ -> (false,b)

(*shold be merged with prune_irr_neq*)
let prune_irr_neq_ll_x p0 irr_svl comps=
  let rec helper p=
    match p with
    | BForm (bf,a) -> let b,nbf = prune_irr_neq_b_form_ll bf irr_svl comps in
      if b then b, mkTrue no_pos else
        false, BForm (nbf,a)
    | And (p1,p2,pos) -> begin
        let b1,np1 = (helper p1) in
        let b2,np2 = (helper p2) in
        match b1,b2 with
        | true,true -> (true, mkTrue no_pos)
        | true,false -> false,np2
        | _, true -> false,np1
        | _ -> (false,mkAnd np1 np2 pos)
      end
    | AndList b-> false,p
    (* let ls_and,svl = List.fold_left (fun (ls1,) (sl,b1) -> *)
    (*     let nb1,svl1 = helper b1 in *)
    (*     if svl1 = [] then ls1@[(sl,b1)],svl0 else *)
    (*       ls1,svl0@svl1 *)
    (* ) ([],[]) b in *)
    (* if svl = [] then (mkTrue no_pos, []) else *)
    (*   AndList ls_and,svl *)
    | Or (b1,b2,_,_) -> (*intersect_svl (helper b1) (helper b2)*)
      false,p
    | Not (b, _,pos) -> let b,np = helper b in
      if b then false,mkFalse no_pos else (false, np)
    | Forall (a,b,c,pos)-> let b,np = helper b in
      if b then b,mkTrue pos else false,Forall (a,np,c,pos)
    | Exists (q,b,lbl,pos)-> let b,np = helper b in
      if b then b,mkTrue pos else (false,Exists (q,np,lbl,pos))
  in
  helper p0

let prune_irr_neq_ll p0 comps=
  let svl = List.concat comps in
  let irr_svl = diff_svl (remove_dups_svl (fv p0)) svl in
  let pr1= !print_formula in
  let pr2 = !print_svl in
  Debug.no_3 "prune_irr_neq_ll" pr1 pr2 (pr_list pr2) (pr_pair string_of_bool pr1)
    (fun _ _ _ -> prune_irr_neq_ll_x p0 irr_svl comps) p0 irr_svl comps

(*************************NEW***********************************)
let prune_irr_neq_b_form_new b irr_svl=
  let (pf,c) = b in
  match pf with
  | Neq (a1, a2, pos)
  | Eq (a1, a2, pos) -> begin
      match a1,a2 with
      | Var (sv1,pos1), Var (sv2,pos2) ->
        if (List.exists (fun sv -> (eq_spec_var sv sv1) || (eq_spec_var sv sv2)) irr_svl) then
          (true,  (BConst (true,pos),c))
        else (false,b)
      | _ -> (false,b)
    end
  | _ -> (false,b)

let prune_irr_neq_new_x p0 irr_svl=
  let rec helper p=
    match p with
    | BForm (bf,a) -> let b,nbf = prune_irr_neq_b_form_new bf irr_svl in
      if b then b, mkTrue no_pos else
        false, BForm (nbf,a)
    | And (p1,p2,pos) -> begin
        let b1,np1 = (helper p1) in
        let b2,np2 = (helper p2) in
        match b1,b2 with
        | true,true -> (true, mkTrue no_pos)
        | true,false -> false,np2
        | _, true -> false,np1
        | _ -> (false,mkAnd np1 np2 pos)
      end
    | AndList b-> false,p
    (* let ls_and,svl = List.fold_left (fun (ls1,) (sl,b1) -> *)
    (*     let nb1,svl1 = helper b1 in *)
    (*     if svl1 = [] then ls1@[(sl,b1)],svl0 else *)
    (*       ls1,svl0@svl1 *)
    (* ) ([],[]) b in *)
    (* if svl = [] then (mkTrue no_pos, []) else *)
    (*   AndList ls_and,svl *)
    | Or (b1,b2,_,_) -> (*intersect_svl (helper b1) (helper b2)*)
      false,p
    | Not (b, _,pos) -> let b,np = helper b in
      if b then false,mkFalse no_pos else (false, np)
    | Forall (a,b,c,pos)-> let b,np = helper b in
      if b then b,mkTrue pos else false,Forall (a,np,c,pos)
    | Exists (q,b,lbl,pos)-> let b,np = helper b in
      if b then b,mkTrue pos else (false,Exists (q,np,lbl,pos))
  in
  helper p0

let prune_irr_neq_new p0 irr_ptrs=
  let pr1= !print_formula in
  let pr2 = !print_svl in
  Debug.no_2 "prune_irr_neq_new" pr1 pr2 (pr_pair string_of_bool pr1)
    (fun _ _ -> prune_irr_neq_new_x p0 irr_ptrs) p0 irr_ptrs


(*************************NEW***********************************)

let is_neg_equality_b neq_bf eq_bf=
  let (pf1,_) = neq_bf in
  let (pf2,_) = eq_bf in
  match (pf1,pf2) with
  |  (Neq(e1, e2, _), Eq(e3, e4, _)) -> ((eqExp e1 e3) && (eqExp e2 e4)) ||
                                        ((eqExp e1 e4) && (eqExp e2 e3))
  | _ -> false

let is_neg_equality neq eq=
  match (neq,eq) with
  | (BForm(c1, _), BForm(c2, _)) -> (is_neg_equality_b c1 c2)
  | _ -> false

let rec inconsisten_neq (f:formula) =
  let helper (bf:b_formula) =
    match bf with
    | (Neq (esv1,esv2,_),_) -> begin
        match esv1,esv2 with
        | Var (sv1,_),Var (sv2,_) -> eq_spec_var sv1 sv2
        | _ -> false
      end
    | _ -> false
  in
  match f with
  | BForm (b,_)-> helper b
  | And (b1,b2,_) -> (inconsisten_neq b1) || (inconsisten_neq  b2)
  | AndList b -> List.exists (fun (_,c)-> inconsisten_neq  c) b
  | Or (b1,b2,_,_) -> (inconsisten_neq  b1) && (inconsisten_neq b2)
  | Not (b,_,_)-> not (inconsisten_neq  b)
  | Forall (_,f,_,_) -> inconsisten_neq f
  | Exists (_,f,_,_) -> inconsisten_neq f
