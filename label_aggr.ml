#include "xdebug.cppo"
open Globals
open VarGen
open Others
open Gen.Basic
open GlobProver
open Mcpure
open Cpure

(* module LO = Label_only.Lab_List *)
module LO = Label_only.LOne
(* open Mcpure_D *)
(* open Log *)
(* open Printf *)

(* code to be moved out later to Label_aggr module for reuse *)

let is_eq_between_no_bag_vars (f:formula) = 
  match f with
  | BForm (bf,_) ->
    (match bf with
     | (Eq (Var (v,_), Var (_,_), _),_) -> if (is_bag_typ v) then false else true
     | _ -> false)
  | _ -> false

(* eset for aggressive labelling *)
let build_eset_of_conj_formula f =
  let lst = split_conjunctions f in
  List.fold_left (fun e f -> match f with
      | BForm (bf,_) ->
        (match bf with
         | (Eq (Var (v1,_), Var (v2,_), _),_) -> 
           if (is_bag_typ v1) then e
           else EMapSV.add_equiv e v1 v2
         | (Eq (ex, Var (v1,_), _),_) 
         | (Eq (Var (v1,_), ex, _),_) -> 
           (match conv_exp_to_var ex with
            | Some (v2,_) -> EMapSV.add_equiv e v1 v2
            | None -> e)
         | _ -> e)
      | _ -> e
    ) EMapSV.mkEmpty lst

let build_eset_of_conj_formula f =
  let pr = !print_formula in
  let pr2 = EMapSV.string_of in
  Debug.no_1 "build_eset_of_conj_formula"  pr pr2  build_eset_of_conj_formula f  

let join_esets es =
  match es with
  | [] -> EMapSV.mkEmpty
  | e::es -> List.fold_left (fun e1 e2 -> EMapSV.merge_eset e1 e2) e es

(* let is_const (s:spec_var) : bool =  *)

(* Andreea : to implement mk_exists for eset *)
(* To be moved later to cpure.ml *)
let mk_exists_eset eset ws =
  EMapSV.elim_elems eset ws

let mk_exists_eset eset ws =
  let pr = string_of_spec_var_list in
  let pr2 = EMapSV.string_of in
  Debug.no_2 "mk_exists_eset"  pr2 pr pr2  mk_exists_eset eset ws

let formula_of_eset eset pos =
  let ep = EMapSV.get_equiv eset in
  List.fold_left (fun f (v1,v2) -> mkAnd f (mkEqVar v1 v2 pos) pos)
    (mkTrue no_pos) ep

let emap_eq_keys key1 key2 =
  Gen.BList.list_setequal_eq EMapSV.eq key1 key2

let emap_eq_pair_keys (key_1a,key_1b)  (key_2a, key_2b) =
  (emap_eq_keys key_1a key_2a && emap_eq_keys key_1b key_2b) ||
  (emap_eq_keys key_1a key_2b && emap_eq_keys key_1b key_2a)

let emap_key_pair_in_list pair_keys list_pair_keys = 
  Gen.BList.mem_eq emap_eq_pair_keys  pair_keys list_pair_keys

(* filters ep by eliminating those pairs which 
   (i)  are already present in em_i or 
   (ii) capture an alias between vars from two different partitions in em_i, but this info is already captured by other pair(s) *)

(* WN : keys for eset has changed to some random value *)

let filter_redundant_eset_pairs ep em_i =
  ep
(* let covered_keys = ref [] in *)
(* List.filter (fun (v1,v2) ->  *)
(*     let key1 = (EMapSV.find em_i v1) in *)
(*     let key2 = (EMapSV.find em_i v2) in *)
(*     (\* same non-empy keys --> same partition in em_i *\) *)
(*     if (List.length (key1@key2) > 0) && (emap_eq_keys key1 key2) then false *)
(*     else  *)
(*       (\* different non-empty partitions from em_i for which alias info is already available *\) *)
(*       if (List.length key1 > 0 && List.length key2 > 0) && (emap_key_pair_in_list (key1,key2) !covered_keys ) then false *)
(*       else *)
(*         begin *)
(*           covered_keys := (key1,key2)::(!covered_keys); *)
(*           true *)
(*         end *)
(* )  ep *)

let formula_of_filtered_eset eset em_i pos =
  let ep = EMapSV.get_equiv eset in
  let ep = filter_redundant_eset_pairs ep em_i in
  (not(ep==[]),List.fold_left (fun f (v1,v2) -> mkAnd f (mkEqVar v1 v2 pos) pos)
     (mkTrue no_pos) ep)

(* operations on list of labelled formula *)
(* to ensure that they are normalized? *)

let combine_lbl_lst ls =
  let rec aux l f ls =
    match ls with
    | [] -> [(l,f)]
    | (l2,f2)::ls -> 
      if LO.is_equal l l2
      then aux l (mkAnd f f2 no_pos) ls
      else (l,f)::(aux l2 f2 ls)
  in match ls with
  | [] -> []
  | (l,f)::ls -> aux l f ls

let norm_lbl_lst lst = 
  let pr = pr_list (pr_pair LO.string_of !print_formula) in
  let nl = List.sort (fun (l1,_) (l2,_) -> LO.compare l1 l2) lst in
  let r = combine_lbl_lst nl in
  if not(List.length r==List.length lst) then
    begin
      Debug.info_pprint "Normalization of Labelled Branches" no_pos;
      Debug.info_hprint (add_str "lbl_norm(before)" pr) lst no_pos;
      Debug.info_hprint (add_str "lbl_norm(after)" pr) r no_pos;
    end
;r

let norm_lbl_lst lst = 
  let pr = pr_list (pr_pair LO.string_of !print_formula) in
  Debug.no_1 "norm_lbl_lst" pr pr norm_lbl_lst lst

let merge_in_rhs lhs rhs =
  let rec aux lhs rhs =
    match lhs,rhs with
    | [],rhs -> []
    | lhs,[] -> List.map (fun (a,b) -> (a,b,[])) lhs
    | (eq,((l1,f1) as n1))::lhs2,(l2,f2)::rhs2 ->
      let n = LO.compare l1 l2 in
      if n<0 then (eq,n1,[])::(aux lhs2 rhs)
      else if n>0 then aux lhs rhs2
      else (eq,n1,(fv f2))::(aux lhs2 rhs)
  in aux lhs rhs

let map_lbl_lst_to_eset lst =
  List.map (fun (l,f) ->
      let es = 
        if LO.is_common l then build_eset_of_conj_formula f
        else EMapSV.mkEmpty
      in
      (es, (l, f))
    ) lst 

let extract_eset_of_lbl_lst lst rhs =
  let lst = norm_lbl_lst lst in
  let rhs = norm_lbl_lst rhs in
  let ls = map_lbl_lst_to_eset lst in
  let ls2 = merge_in_rhs ls rhs in
  let eq_all = join_esets (List.map fst ls) in
  let es = EMapSV.get_elems  eq_all in
  let n_lst = List.map 
      (fun (em_f,(l,f),rhs_vs) ->
         if LO.is_common l then (l,f)
         else
           let vs = (fv f)@rhs_vs in
           x_tinfo_hp (add_str "vars_from_fv" string_of_spec_var_list) vs no_pos;
           let vs = List.filter (fun v -> not(is_const v)) vs in
           let ws = Gen.BList.difference_eq eq_spec_var es vs in
           let r = mk_exists_eset eq_all ws in
           let (flag,r) = formula_of_filtered_eset r em_f no_pos in
           if flag then
             begin
               x_tinfo_hp (add_str "\n f" !print_formula) f no_pos;
               x_tinfo_hp (add_str "eq_to_add" !print_formula) r no_pos
             end;
           let nf = mkAnd r f no_pos in
           (l,nf)
      ) ls2
  in n_lst
(* let () = Debug.info_hprint (add_str "mkE eqall" EMapSV.string_of) eq_all no_pos in *)
(* let () = Debug.info_hprint (add_str "mkE ws" string_of_spec_var_list) ws no_pos in *)
(* let r = formula_of_eset r no_pos in *)

let extract_eset_of_lbl_lst lst rhs =
  let pr = pr_list (pr_pair LO.string_of !print_formula) in
  (* let pr2 = pr_list (!print_formula) in *)
  Debug.no_1 "extract_eset_of_lbl_lst"  pr pr  (fun _ -> extract_eset_of_lbl_lst lst rhs) lst  


(* let extract_eq_clauses_formula f =  *)
(*   let lst = split_conjunctions f in *)
(*   List.filter is_eq_between_no_bag_vars lst *)

(*
 E1=eq(S1) E2=eq(S2) E=E1&E2 W=fv(E)
 V1=fv(S1) V2=fv(S2)
 R1=ex(W-V1.E) R2=ex(W-V2.E)
 SAT(R1 & S1) | SAT(R2 & S2)
-----------------------------
 SAT(S1 & S2)
*)


(* let extract_eq_clauses_lbl_lst lst = *)
(*   let ls = List.map (fun (l,f) ->  *)
(*       if LO.is_common l then extract_eq_clauses_formula f *)
(*       else [] *)
(*   ) lst in *)
(*   let eq_all = join_conjunctions (List.concat ls) in *)
(*   let es = fv eq_all in *)
(*   let n_lst = List.map (fun (l,f) -> *)
(*       if Label_only.Lab_List.is_common l then (l,f) *)
(*       else  *)
(*         let vs = fv f in *)
(*         let ws = Gen.BList.difference_eq eq_spec_var es vs in *)
(*         let r = wrap_exists_svl eq_all ws in *)
(*         let nf = mkAnd r f no_pos in *)
(*         (l,nf) *)
(*   ) lst  *)
(*   in n_lst *)
(* let rec aux conjs lst =  *)
(*   match lst with *)
(*     | []   -> (conjs, []) *)
(*     | (lbl,f)::t -> *)
(*           let eq_f_lst = extract_eq_clauses_formula f in *)
(*           let (all_eq, tail) = aux (conjs@eq_f_lst) t in *)
(*           let eqs_to_add = Gen.BList.difference_eq (equalFormula) all_eq eq_f_lst in *)
(*           let conj = join_conjunctions eqs_to_add in *)
(*           (\* let new_f = mkAnd f conj no_pos in *\) *)
(*           (all_eq, (lbl,conj)::tail) *)
(* in  *)
(* snd (aux [] lst) *)

(* let extract_eq_clauses_lbl_lst lst = *)
(*   let pr = pr_list (pr_pair pr_none !print_formula) in *)
(*   let pr2 = pr_list (!print_formula) in *)
(*   Debug.no_1 "extract_eq_clauses_lbl_lst"  pr pr  extract_eq_clauses_lbl_lst lst   *)
