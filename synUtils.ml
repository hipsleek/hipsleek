#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Others
open Label_only
module CP = Cpure
module IF = Iformula
module CF = Cformula
module MCP = Mcpure

let mem = Gen.BList.mem_eq CP.eq_spec_var
let diff = Gen.BList.difference_eq CP.eq_spec_var

let eq_id s1 s2 = String.compare s1 s2 == 0

let mem_id = Gen.BList.mem_eq eq_id

let rec partition_by_key key_of key_eq ls = 
  match ls with
  | [] -> []
  | e::es ->
    let ke = key_of e in 
    let same_es, other_es = List.partition (fun e -> key_eq ke (key_of e)) es in
    (ke, e::same_es)::(partition_by_key key_of key_eq other_es)

let simplify f args = 
  let bnd_vars = diff (CP.fv f) args in
  if bnd_vars == [] then f else
    CP.mkExists_with_simpl Tpdispatcher.simplify_raw bnd_vars f None (CP.pos_of_formula f)

(*****************)
(***** UTILS *****)
(*****************)
let is_pre_hprel (hpr: CF.hprel) = 
  (* match hpr.hprel_proving_kind with *)
  (* | PK_PRE                          *)
  (* | PK_PRE_REC -> true              *)
  (* | _ -> false                      *)
  true

let is_post_hprel (hpr: CF.hprel) = 
  (* match hpr.hprel_proving_kind with *)
  (* | PK_POST -> true                 *)
  (* | _ -> false                      *)
  false

let sig_of_hrel (h: CF.h_formula) =
  match h with
  | HRel (hr_sv, hr_args, _) -> (hr_sv, CF.get_node_args h)
  | _ -> failwith ("Expected a HRel h_formula instead of " ^ (!CF.print_h_formula h))

let name_of_hrel (h: CF.h_formula) = 
  fst (sig_of_hrel h) 

let args_of_hrel (h: CF.h_formula) = 
  snd (sig_of_hrel h)

let sig_of_hprel (hpr: CF.hprel) =
  let hpr_f = if is_pre_hprel hpr then hpr.hprel_lhs else hpr.hprel_rhs in
  let f_h, _, _, _, _, _ = CF.split_components hpr_f in
  match f_h with
  | HRel (hr_sv, hr_args, _) -> (hr_sv, CF.get_node_args f_h)
  | _ -> failwith ("Unexpected formula in the LHS/RHS of a hprel " ^ (Cprinter.string_of_hprel_short hpr))

let name_of_hprel (hpr: CF.hprel) = 
  fst (sig_of_hprel hpr) 

let args_of_hprel (hpr: CF.hprel) = 
  snd (sig_of_hprel hpr)

(**********************)
(* UTILS OVER FORMULA *)
(**********************)
let is_non_inst_hprel prog (hprel: CF.hprel) =
  let hprel_name = CP.name_of_spec_var (name_of_hprel hprel) in
  let hprel_def = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls hprel_name in
  let hprel_inst = hprel_def.Cast.hp_vars_inst in
  List.for_all (fun (_, i) -> i = Globals.NI) hprel_inst

let is_non_inst_hrel prog (hrel: CF.h_formula) =
  let hrel_name = CP.name_of_spec_var (name_of_hrel hrel) in
  let hrel_def = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls hrel_name in
  let hrel_inst = hrel_def.Cast.hp_vars_inst in
  List.for_all (fun (_, i) -> i = Globals.NI) hrel_inst

let get_feasible_node_args prog (hf: CF.h_formula) =
  match hf with
  | HRel (hrel, el, _) ->
    let hrel_name = CP.name_of_spec_var hrel in
    let hprel_def = Cast.look_up_hp_def_raw prog.Cast.prog_hp_decls hrel_name in
    let el_inst = 
      try List.combine el (List.map snd hprel_def.Cast.hp_vars_inst)
      with Invalid_argument _ -> failwith ("SynUtils: Number of arguments of HRel " ^ hrel_name ^ " mismatched.")
    in
    List.fold_left (fun acc (e, i) ->
        match e with
        | CP.Var (sv, _) -> if i = Globals.NI then acc else acc @ [sv]
        | _ -> failwith ("Unexpected exp (not CP.Var) in HRel " ^ hrel_name ^ "'s arguments.")) 
      [] el_inst
  | _ -> CF.get_node_args hf

let collect_feasible_heap_args_formula prog null_aliases (f: CF.formula) : CP.spec_var list = 
  let rec helper f = 
    match f with
    | CF.Base ({ formula_base_heap = h; formula_base_pure = p; })
    | CF.Exists ({ formula_exists_heap = h; formula_exists_pure = p; }) ->
      let heaps = CF.split_star_conjunctions h in
      let heaps = List.filter (fun h ->
          match h with | CF.HEmp | CF.HTrue -> false | _ -> true) heaps
      in
      let heap_args = Gen.BList.remove_dups_eq CP.eq_spec_var 
          (List.concat (List.map (fun h ->
            let heap_node = try [CF.get_node_var h] with _ -> []
            in heap_node @ (get_feasible_node_args prog h)) heaps)) in
      if is_empty null_aliases then heap_args
      else
        List.filter (fun arg -> Gen.BList.mem_eq CP.eq_spec_var arg null_aliases) heap_args
    | CF.Or ({ formula_or_f1 = f1; formula_or_f2 = f2; }) ->
      (helper f1) @ (helper f2)
  in helper f

let collect_feasible_heap_args_formula prog null_aliases (f: CF.formula) : CP.spec_var list = 
  Debug.no_2 "collect_feasible_heap_args_formula" !CP.print_svl !CF.print_formula !CP.print_svl
    (collect_feasible_heap_args_formula prog) null_aliases f