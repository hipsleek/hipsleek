#include "xdebug.cppo"
open Globals
open VarGen
open Gen

module CP = Cpure

(*****************************************************************)
(**simplify/hul/pairwise check - disjuncts normalization **)
(*****************************************************************)

type disj_tree = Empty | Node of  (CP.Label_Pure.exp_ty list) * (disj_tree list)

let string_of_disj_tree tree =
  let rec aux tree =
    match tree with
    | Empty -> " [] "
    | Node (content, children) -> let pr = pr_pair (pr_list Cprinter.string_of_pure_formula) (pr_list aux) in
      pr (content, children)
  in aux tree


let finalize_norm f1_conj f2_conj common_conj =
  let f1   = CP.join_conjunctions f1_conj in
  let f2   = CP.join_conjunctions f2_conj in
  let disj = CP.mkOr f1 f2 None no_pos in
  CP.join_conjunctions (common_conj@[disj])

let make_strict_ieq ieq =
  match ieq with
  | CP.BForm (b, lb) ->
    begin
      match b with
      | (CP.Lte (CP.IConst (i, loci), (CP.Var(v,_) as var), s), l)
      | (CP.Gte ((CP.Var(v,_) as var),CP.IConst (i, loci),  s), l) ->  CP.BForm ((CP.Lt (CP.IConst ((i-1), loci), var, s), l), lb)
      | (CP.Lte ((CP.Var(v,_) as var), CP.IConst (i, loci), s), l)
      | (CP.Gte (CP.IConst (i, loci), (CP.Var(v,_) as var), s), l) ->  CP.BForm ((CP.Lt (var, CP.IConst ((i+1), loci), s), l), lb)
      | _ -> ieq
    end
  | _ -> ieq


let simplif_arith f =
  match f with
  | CP.BForm (b, lb) ->
    begin
      let b = 
        match b with
        | (CP.Lte (e1, e2, s), l) ->  (CP.Lte (CP.norm_exp e1,CP.norm_exp e2, s), l)
        | (CP.Lt (e1, e2, s), l) ->  (CP.Lt (CP.norm_exp e1,CP.norm_exp e2, s), l)
        | (CP.Gte (e1, e2, s), l) ->  (CP.Lte (CP.norm_exp e2,CP.norm_exp e1, s), l)
        | (CP.Gt (e1, e2, s), l) ->  (CP.Lt (CP.norm_exp e2,CP.norm_exp e1, s), l)
        | (CP.Eq  (e1, e2, s), l) ->  (CP.Eq  (CP.norm_exp e1,CP.norm_exp e2, s), l)
        | (CP.Neq (e1, e2, s), l) ->  (CP.Neq (CP.norm_exp e1,CP.norm_exp e2, s), l)
        | _ -> b
      in CP.BForm(b, lb)
    end
  | _ -> f


let merge_other f1 f2 = (false, [])

(* this limits the number of conjunct *)
let limit_conj = 2

let list_of_n n start =
  let rec aux n top lst =
    if n == 0 then lst@[top]
    else (aux (n-1) (top-1) lst@[top]) 
  in aux n start []

let neq_conj_n n bot var =
  let lst_n = list_of_n n bot in
  let f_conj = List.map (fun i ->  (CP.BForm((CP.mkNeq var (CP.mkIConst i no_pos) no_pos, None), None))) lst_n in
  f_conj

let conv_exp_to_var e = 
  match e with
  | CP.IConst(i, _) -> Some (CP.mk_sp_const i)
  | CP.Null _ -> Some CP.null_var
  | CP.Var(v, _) -> Some v
  | _ -> None

let merged f = (true, f)

let merge_ieq_ieq f1 f2  =  (* merge_other f1 f2 *)
  match f1, f2 with
  | CP.BForm (b1, _), CP.BForm (b2, _) ->
    begin
      match b1,b2 with
      (* i1<v1 | i2<v2 *)
      | (CP.Lt (CP.IConst (i1, _), CP.Var(v1,_), _), _), (CP.Lt (CP.IConst (i2, loci), CP.Var(v2,_), _), _) ->
        if (CP.eq_spec_var v1 v2) then
          if i1<=i2 then merged [f1] else merged [f2]
        else merge_other f1 f2
      (* v1<i1 | v2<i2 *)
      | (CP.Lt (CP.Var(v1,_) , CP.IConst (i1, _), _), _), (CP.Lt (CP.Var(v2,_), CP.IConst (i2, loci), _), _) ->
        if (CP.eq_spec_var v1 v2) then
          if i1<=i2 then merged [f2] else merged [f1]
        else merge_other f1 f2
      (* i1<v1 | v2<i2 *)
      | (CP.Lt (CP.IConst (i1, _), CP.Var(v1,_), _), _), (CP.Lt ((CP.Var(v2,_) as var), CP.IConst (i2, loci), _), _)
      (* v2<i2 | i1<v1 *)
      | (CP.Lt ((CP.Var(v2,_) as var), CP.IConst (i2, loci), _), _), (CP.Lt (CP.IConst (i1, _), CP.Var(v1,_), _), _) ->
        if (CP.eq_spec_var v1 v2) then
          if i1<i2 then  merged [CP.mkTrue no_pos]
          else 
          if((i1-i2) < limit_conj) then merged (neq_conj_n (i1-i2) i1 var)
          else merge_other f1 f2
        else merge_other f1 f2
      (* v1<v2 | v3<i4 *)
      | (CP.Lt ( (CP.Var(v1,_) as var1), (CP.Var(v2,_) as var2), _), _), (CP.Lt (CP.Var(v3,_),CP.Var(v4,_), _), _) ->
        if (CP.eq_spec_var v1 v4) && (CP.eq_spec_var v2 v3) then merged [(CP.BForm((CP.mkNeq var1 var2 no_pos, None), None))] (* a<b | b<a *)
        else merge_other f1 f2
      | _ -> merge_other f1 f2
    end
  | _ -> merge_other f1 f2



let merge_eq_ieq eq ieq  = merge_other eq ieq
(* let emap = CP.EMapSV.build_eset ( CP.pure_ptr_equations eq) in *)
(* match ieq with *)
(*   | CP.BForm (b, lb) -> *)
(*         begin *)
(*           match b with *)
(*             | (CP.Lt (ex1, ex2, s), l) ->  *)
(*                   begin *)
(*                     match conv_exp_to_var ex1, conv_exp_to_var ex2 with *)
(*                       |  Some v1, Some v2 -> *)
(*                              if CP.EMapSV.is_equiv emap v1 v2 then  *)
(*                                  merged [CP.BForm ((CP.Lte (ex1,  ex2, s), l), lb)] *)
(*                              else merge_other eq ieq *)
(*                       | _, _ -> merge_other eq ieq *)
(*                   end *)
(*             | (CP.Gt (ex1, ex2, s), l) -> *)
(*                   begin *)
(*                     match conv_exp_to_var ex1, conv_exp_to_var ex2 with *)
(*                       |  Some v1, Some v2 -> *)
(*                              if CP.EMapSV.is_equiv emap v1 v2 then *)
(*                                merged [CP.BForm ((CP.Gte (ex1,  ex2, s), l), lb)] *)
(*                              else merge_other eq ieq *)
(*                       | _, _ -> merge_other eq ieq *)
(*                   end *)
(*             | (CP.Neq (ex1, ex2, _), _) -> *)
(*                   begin *)
(*                     match conv_exp_to_var ex1, conv_exp_to_var ex2 with *)
(*                       |  Some v1, Some v2 -> *)
(*                              if CP.EMapSV.is_equiv emap v1 v2 then  *)
(*                                  merged [CP.mkTrue no_pos] *)
(*                              else merge_other eq ieq *)
(*                       | _, _ -> merge_other eq ieq *)
(*                   end *)
(*             | _ -> merge_other eq ieq *)
(*         end *)
(*   | _ -> merge_other eq ieq *)

let merge_eq_eq f1 f2 = merge_other f1 f2

let merge_two_disj f1 f2 = 
  let f1 = simplif_arith f1 in
  let f2 = simplif_arith f2 in
  let f1 = make_strict_ieq f1 in
  let f2 = make_strict_ieq f2 in
  match CP.is_ieq f1, CP.is_ieq f2 with
  | true, true ->  merge_ieq_ieq  f1 f2 
  | false, true ->  if CP.is_eq_exp f1 then merge_eq_ieq f1 f2  else  merge_other f1 f2
  | true, false ->  if CP.is_eq_exp f2 then merge_eq_ieq f2 f1  else  merge_other f1 f2
  | false, false -> if (CP.is_eq_exp f1) && (CP.is_eq_exp f2) then merge_eq_eq f1 f2 else  merge_other f1 f2

let can_further_norm f1_conj f2_conj =
  let f1_sv = List.fold_left (fun a f ->  (CP.all_vars f)@a) [] f1_conj in
  let f2_sv = List.fold_left (fun a f ->  (CP.all_vars f)@a) [] f2_conj in
  if Gen.BList.list_setequal_eq CP.eq_spec_var f1_sv f2_sv then true
  else false

let maybe_merge conj1i conj2i = (* (true, conj1) *)
  let common_conj, conj1 = List.partition (fun f -> Gen.BList.mem_eq CP.equalFormula f conj2i) conj1i in
  let conj2 = Gen.BList.difference_eq CP.equalFormula conj2i common_conj in
  match conj1, conj2 with
  | [], [] -> (true,conj1i)                     (* identical lists*)
  | _, []
  | [], _  -> (true, common_conj)
  | f1::[], f2::[] -> 
    if can_further_norm [f1] [f2] then 
      let merged, new_f = merge_two_disj f1 f2 in
      (merged,common_conj@new_f)
    else
      (false,[])
  | _, _   -> 
    if can_further_norm conj1 conj2 then 
      (* let norm = norm_disj_lsts f1_conj f2_conj in *)
      (* CP.join_conjunctions (common_conj@[norm]) *)
      (false,[])
    else                          (* formulas can not be further normalized *)
      (false,[])

let maybe_merge conj1 conj2 =
  let pr = pr_list Cprinter.string_of_pure_formula in
  let pr_out = pr_pair string_of_bool pr in
  Debug.no_2 "maybe_merge" pr pr pr_out maybe_merge conj1 conj2

let update_disj disj conj_lst = 
  let rec helper disj (conj_lst,d_init) =
    match disj with
    | []    -> (None, [Node(conj_lst, d_init)])
    | x::xs -> 
      match x with
      | Empty -> (Some (Node (conj_lst,d_init)), xs)
      | Node (conj, d) -> 
        let (merged, new_conj) = maybe_merge conj conj_lst in 
        if merged then
          (Some (Node (new_conj,d_init@d)), xs)
        else 
          let merged_node, disj = helper xs (conj_lst,d_init) in
          (merged_node, disj@[x])
  in
  let rec aux disj (conj_lst, d) =
    let merged_node, disj = helper disj (conj_lst,d)  in
    match merged_node with 
    | Some Node (conj, d) -> aux disj (conj,d)
    | _ -> disj
  in
  aux disj (conj_lst,[])

(* adds a new disjunct(conj_lst) to the existing tree  *)
let add_disj_to_tree conj_lst tree =
  match tree with
  | Empty -> Node(conj_lst, [Empty])
  | Node (common, disjT) -> 
    (* new_common <-- conj_lst \intersect common; push_back = common\conj_lst *)
    let new_common, push_back = List.partition (fun c-> Gen.BList.mem_eq CP.equalFormula c conj_lst) common in
    let new_disjT = List.map (fun d -> 
        match d with
        | Empty -> Node(push_back, [])
        | Node (c,d) -> Node (c@push_back, d) ) disjT in
    let conj_lst = Gen.BList.difference_eq  CP.equalFormula conj_lst new_common in (* grep only what's not common with the root *)
    (* let new_disj = Empty::new_disj in (\* Empty is the placeholder for conj_lst in case the latter can not merge with other  *\) *)
    let new_disjT = update_disj new_disjT conj_lst in
    Node(new_common, new_disjT)

(* creates the tree of disjunctions *)
let norm_disj_tree disj = 
  let rec helper disj tree =
    match disj with
    | x::xs -> 
      let tree = add_disj_to_tree x tree in
      helper xs tree
    | []    -> tree
  in
  let tree = helper disj Empty in
  tree

let norm_disj_tree disj = 
  let pr = pr_list (pr_list Cprinter.string_of_pure_formula) in
  Debug.no_1 "norm_disj_tree" pr string_of_disj_tree norm_disj_tree disj

let formula_of_tree tree = 
  let rec aux tree = 
    match tree with
    | Empty -> CP.mkTrue no_pos
    | Node (common, disj) -> 
      (* let common = CP.join_conjunctions common in *)
      let disj = List.filter (fun t -> match t with | Empty -> false  | _ -> true ) disj in
      let disj_clause = CP.join_disjunctions (List.map aux disj) in
      CP.join_conjunctions (common@[disj_clause] )
  in aux tree

let formula_of_tree tree = 
  Debug.no_1 "formula_of_tree" string_of_disj_tree Cprinter.string_of_pure_formula formula_of_tree tree 

let norm_disj f = 
  let disj = List.map CP.split_conjunctions (CP.split_disjunctions f) in
  let f = formula_of_tree (norm_disj_tree disj) in
  f

let norm_disj f = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "norm_disj" pr pr norm_disj f
(*****************************************************************)
(**END simplify/hul/pairwise check - disjuncts normalization **)
(*****************************************************************)
