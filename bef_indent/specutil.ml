#include "xdebug.cppo"
open VarGen
open Globals
module DD = Debug
open Gen
open Exc.GTable
open Cformula
open Cpure
open Cprinter

module CP = Cpure
module MCP = Mcpure
module CF = Cformula
module TP = Tpdispatcher
module IF = Iformula
module I = Iast
module C = Cast

type pure_dom = {
  para_names : spec_var list;
  (* TODO *)
(*  inductive_def : ...;*)
}

(******************************************************************************)

let rec size_of_heap (fml:CF.h_formula) : (CP.exp*CP.p_formula list) = match fml with
  | Star {h_formula_star_h1 = h1;
    h_formula_star_h2 = h2;
    h_formula_star_pos = pos} -> 
    let res1 = size_of_heap h1 in
    let res2 = size_of_heap h2 in
    (Add (fst res1,fst res2,pos), snd res1 @ snd res2)
  | Conj {h_formula_conj_h1 = h1;
    h_formula_conj_h2 = h2;
    h_formula_conj_pos = pos} ->
    let res1 = size_of_heap h1 in
    let res2 = size_of_heap h2 in
    (Add (fst res1,fst res2,pos), snd res1 @ snd res2)
  | Phase _ -> report_error no_pos "size_of_heap: Do not expect Phase"
  | DataNode _ -> (IConst (1,no_pos), [])
  | ViewNode vn -> 
    let v = List.hd (List.rev vn.h_formula_view_arguments) in
    let p = Var (v,no_pos) in
    let rel = RelForm (SpecVar (RelT[], vn.h_formula_view_name, Unprimed), [p], no_pos) in
    (p,[rel])
  | Hole _ -> report_error no_pos "size_of_heap: Do not expect Hole"
  | HRel _ -> report_error no_pos "size_of_heap: Do not expect HRel"
  | HTrue
  | HFalse
  | HEmp -> (IConst (0,no_pos),[])
  

let size_of_fml (fml:CF.formula) (lhs_para:CP.spec_var): (CF.formula * CP.formula) = match fml with
  | CF.Or _ -> report_error no_pos "size_of_fml: Do not expect Or formula"
  | CF.Base b -> 
    let p,rel = size_of_heap b.formula_base_heap in
    let pure = mkEqExp (Var (lhs_para,no_pos)) p no_pos in
    let rels = List.map (fun r -> BForm ((r,None),None)) rel in
    let pure2 = List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) pure rels in
    let mix = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix b.formula_base_pure) pure no_pos) in
    (CF.Base {b with formula_base_pure = mix}, pure2)
  | CF.Exists e -> 
    let p,rel = size_of_heap e.formula_exists_heap in
    let pure = mkEqExp (Var (lhs_para,no_pos)) p no_pos in
    let rels = List.map (fun r -> BForm ((r,None),None)) rel in
    let pure2 = List.fold_left (fun f1 f2 -> CP.mkAnd f1 f2 no_pos) pure rels in
    let mix = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix e.formula_exists_pure) pure no_pos) in
    (CF.Exists {e with formula_exists_pure = mix}, pure2)

let rec size_of (fml:CF.struc_formula) (lhs_para:CP.spec_var): (CF.struc_formula*CP.formula list) =
  match fml with
  | ECase b -> 
    let res = List.map (fun (p,c) -> 
      let r = size_of c lhs_para in
      ((p,fst r),snd r)) b.formula_case_branches in
    let r1,r2 = List.split res in
    (ECase {b with formula_case_branches = r1}, List.concat r2)
  | EBase b -> 
    let rbase = size_of_fml b.formula_struc_base lhs_para in
    let rcont = (match b.formula_struc_continuation with
      | None -> (None,[])
      | Some f -> let r = size_of f lhs_para in
        (Some (fst r),snd r)) in
    (EBase {b with 
      formula_struc_base = fst rbase;
      formula_struc_continuation = fst rcont}, (snd rbase) :: (snd rcont))
  | EAssume(svl,f,fl,t) -> let r = size_of_fml f lhs_para in
    (EAssume(svl,fst r,fl,t),[snd r])
  | EInfer b -> let r = size_of b.formula_inf_continuation lhs_para in
    (EInfer {b with formula_inf_continuation = fst r}, snd r)
  | EList b -> 
    let res = List.map (fun (l,e) -> 
      let r = size_of e lhs_para in
      ((l,fst r),snd r)) b in
    let r1,r2 = List.split res in
    (EList r1,List.concat r2)
  | EOr b -> 
    let r1 = size_of b.formula_struc_or_f1 lhs_para in
    let r2 = size_of b.formula_struc_or_f2 lhs_para in
    (EOr {b with formula_struc_or_f1 = fst r1;
                formula_struc_or_f2 = fst r2}, snd r1 @ snd r2)

(******************************************************************************)

let gen_struc_fml (orig_fml:CF.struc_formula) (abs_dom:pure_dom) sub_pair: (CF.struc_formula*CP.formula list) =
  let updated_fml = CF.tran_spec orig_fml sub_pair in
  let new_fml,new_pures = size_of (fst updated_fml) (List.hd abs_dom.para_names) in
  new_fml,new_pures

(* TODO: abs_dom *)
(* Primitive case: size(). See more in gen_pred.txt *)
let gen_pred_def (orig_def:C.view_decl) (abs_dom:pure_dom): C.view_decl =
  let new_view_name = fresh_old_name orig_def.C.view_name in
  let new_view_vars = orig_def.C.view_vars @ abs_dom.para_names in
  let sub_pair = ((orig_def.C.view_name,orig_def.C.view_vars),(new_view_name,new_view_vars)) in
  let new_fml,new_pures = gen_struc_fml orig_def.C.view_formula abs_dom sub_pair in
  let additional_inv = Fixcalc.compute_pure_inv new_pures new_view_name abs_dom.para_names in
  let new_inv = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix orig_def.C.view_user_inv) additional_inv no_pos) in
  let new_def = {orig_def with
    C.view_name = new_view_name;
    C.view_vars = new_view_vars;
    C.view_formula = new_fml;
    C.view_user_inv = new_inv;}
  in new_def

let string_of_view_decl v =
  let rec string_of_elems elems string_of sep = match elems with 
    | [] -> ""
    | h::[] -> string_of h 
    | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)
  in
  v.C.view_name ^ "<" ^ (string_of_elems v.C.view_vars string_of_spec_var ",") ^ "> == " ^
  (string_of_struc_formula v.C.view_formula) ^ "inv " ^ 
  (string_of_mix_formula v.C.view_user_inv) ^ ";"


let test prog =
  let orig_def = List.hd prog.C.prog_view_decls in
  let () = print_endline_quiet ("\n\n" ^ string_of_view_decl orig_def) in
  let () = print_endline_quiet "\n\n" in
  let abs_dom = {para_names = [SpecVar (Int, "n", Unprimed)]} in
  let new_def = gen_pred_def orig_def abs_dom in
  print_endline_quiet (string_of_view_decl new_def)






