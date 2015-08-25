#include "xdebug.cppo"
open VarGen
(*
  Call FixBag, send input to it
*)

open Globals
module DD = Debug
open Gen
open Exc.GTable
open Perm
open Cpure
open Context
module M = Lexer.Make(Token.Token)

module Pr = Cprinter
module CP = Cpure
module CF= Cformula
module MCP = Mcpure
module TP = Tpdispatcher

(* Operators *)
let op_lt = "<" 
let op_lte = "<=" 
let op_gt = ">" 
let op_gte = ">=" 
let op_eq = "=" 
let op_neq = "!=" 
let op_and = " && "
let op_or = " || "
let op_add = "+"
let op_sub = "-"

(*let is_self = CP.is_self_var*)

(*let is_null = CP.is_null*)

let rec string_of_elems elems string_of sep = match elems with 
  | [] -> ""
  | h::[] -> string_of h 
  | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)

let fixbag_of_spec_var x = match x with
  (*  | CP.SpecVar (Named _, id, Unprimed) -> "NOD" ^ id*)
  (*  | CP.SpecVar (Named _, id, Primed) -> "NODPRI" ^ id*)
  (*  | CP.SpecVar (_, id, Unprimed) -> id*)
  (*  | CP.SpecVar (_, id, Primed) -> "PRI" ^ id*)
  | CP.SpecVar (_, id, _) -> if is_anon_var x && not (is_bag_typ x) then "v_" ^ id else id

let rec fixbag_of_exp e = match e with
  | CP.Null _ -> "null"
  | CP.Var (x, _) -> fixbag_of_spec_var x
  | CP.IConst (i, _) -> string_of_int i
  (*  | CP.FConst (f, _) -> string_of_float f*)
  | CP.Add (e1, e2, _) -> fixbag_of_exp e1 ^ op_add ^ fixbag_of_exp e2 
  | CP.Subtract (e1, e2, _) -> fixbag_of_exp e2
  | CP.Bag (es, _) -> "{" ^ (string_of_elems es fixbag_of_exp ",") ^ "}"
  | CP.BagUnion (es, _) -> string_of_elems es fixbag_of_exp "+"
  | CP.BagIntersect (es, _) -> string_of_elems es fixbag_of_exp "."
  | CP.BagDiff (e1, e2, _) -> fixbag_of_exp e1 ^ op_sub ^ fixbag_of_exp e2 
  | _ -> illegal_format ("Fixbag.fixbag_of_exp: Not supported expression")

let rec fixbag_of_b_formula b =
  let (pf, _) = b in
  match pf with
  | CP.BConst (b,_) -> "{}={}"
  | CP.BVar (x, _) -> fixbag_of_spec_var x
  | CP.Lt (e1, e2, _) -> "{}={}"
  | CP.Lte (e1, e2, _) -> "{}={}"
  | CP.Gt (e1, e2, _) -> "{}={}"
  | CP.Gte (e1, e2, _) -> "{}={}"
  | CP.Eq (e1, e2, _) -> if CP.is_null e2 && not (is_bag e1) then fixbag_of_exp e1 ^op_lte^"0"
    else if CP.is_null e1 && not(is_bag e2) then fixbag_of_exp e2 ^op_lte^"0"
    else fixbag_of_exp e1 ^ op_eq ^ fixbag_of_exp e2
  | CP.Neq (e1, e2, _) -> 
    if CP.is_null e2 && not (is_bag e1) then fixbag_of_exp e1 ^op_gt^"0"
    else if CP.is_null e1 && not(is_bag e2) then fixbag_of_exp e2 ^op_gt^"0"
    else if (* !allow_pred_spec *) not !dis_ps && (List.exists is_bag_typ (CP.bfv b) || is_bag e1 || is_bag e2) then "{}={}"
    else
    if List.exists is_int_typ (CP.bfv b) then fixbag_of_exp e1 ^ op_neq ^ fixbag_of_exp e2
    else "!(" ^ fixbag_of_exp e1 ^ op_eq ^ fixbag_of_exp e2 ^ ")"
  | CP.RelForm (id,args,_) -> (fixbag_of_spec_var id) ^ "(" ^ (string_of_elems args fixbag_of_exp ",") ^ ")"
  (*    | BagIn (sv, e, _) ->*)
  (*    | BagNotIn (sv, e, _) -> *)
  | CP.BagSub (e1, e2, _) -> fixbag_of_exp e1 ^ op_lte ^ fixbag_of_exp e2
  (*    | BagMin (sv1, sv2, _) ->*)
  (*    | BagMax (sv1, sv2, _) ->*)
  | _ -> illegal_format ("Fixbag.fixbag_of_b_formula: Do not support list or boolean vars")

let rec fixbag_of_pure_formula f = match f with
  | CP.BForm ((CP.BVar (x,_),_),_) -> "$" ^ fixbag_of_spec_var x
  | CP.BForm (b,_) -> fixbag_of_b_formula b
  | CP.And (p1, p2, _) ->
    "(" ^ fixbag_of_pure_formula p1 ^ op_and ^ fixbag_of_pure_formula p2 ^ ")"
  | CP.AndList b -> "(" ^ String.concat op_and (List.map (fun (_,c)-> fixbag_of_pure_formula c) b) ^ ")"
  | CP.Or (p1, p2,_ , _) ->
    "(" ^ fixbag_of_pure_formula p1 ^ op_or ^ fixbag_of_pure_formula p2 ^ ")"
  | CP.Not (p,_ , _) -> 
    begin
      match p with
      | CP.BForm ((CP.BVar (x,_),_),_) -> "!$" ^ fixbag_of_spec_var x
      | _ -> "!(" ^ fixbag_of_pure_formula p ^ ")"
    end
  | CP.Forall (sv, p,_ , _) -> illegal_format ("Fixbag.fixbag_of_pure_formula: Do not support forall")
  (*    " (forall (" ^ fixbag_of_spec_var sv ^ ":" ^ fixbag_of_pure_formula p ^ ")) "*)
  | CP.Exists (sv, p,_ , _) ->
    " (exists " ^ fixbag_of_spec_var sv ^ ":" ^ fixbag_of_pure_formula p ^ ") "

let rec fixbag_of_h_formula f = match f with
  | CF.Star {CF.h_formula_star_h1 = h1; CF.h_formula_star_h2 = h2} -> 
    "(" ^ fixbag_of_h_formula h1 ^ op_and ^ fixbag_of_h_formula h2 ^ ")"
  | CF.Phase _ -> illegal_format ("Fixbag.fixbag_of_h_formula: Not supported Phase-formula")
  | CF.Conj {CF.h_formula_conj_h1 = h1; CF.h_formula_conj_h2 = h2} -> 
    "(" ^ fixbag_of_h_formula h1 ^ op_or ^ fixbag_of_h_formula h2 ^ ")"
  | CF.DataNode {CF.h_formula_data_node = sv; CF.h_formula_data_name = c;CF.h_formula_data_arguments = svs} -> 
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^ (fixbag_of_spec_var sv) ^ "," ^ (string_of_elems svs fixbag_of_spec_var ",") ^ ")"
  | CF.ViewNode {CF.h_formula_view_node = sv; CF.h_formula_view_name = c; CF.h_formula_view_arguments = svs} ->
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^  (fixbag_of_spec_var sv)  ^","^ (string_of_elems svs fixbag_of_spec_var ",")^","^ res_name ^ ")"
  | CF.HTrue -> "HTrue"
  | CF.HFalse -> "HFalse"
  | CF.HEmp -> "{}={}"
  | CF.HRel _ -> "HTrue"
  | CF.Hole _ -> illegal_format ("Fixbag.fixbag_of_h_formula: Not supported Hole-formula")
  | _ -> illegal_format("Fixbag.fixbag_of_h_formula: Not Suppoted")

let fixbag_of_mix_formula (f,l) = match f with
  | MCP.MemoF _ -> ""
  | MCP.OnePF pf -> fixbag_of_pure_formula pf

let rec fixbag_of_formula e = match e with
  | CF.Or _ -> illegal_format ("Fixbag.fixbag_of_formula: Not supported Or-formula")
  | CF.Base {CF.formula_base_heap = h; CF.formula_base_pure = p; CF.formula_base_label = b} ->
    "(" ^ fixbag_of_h_formula h ^ op_and ^ fixbag_of_mix_formula (p,b) ^ ")"
  | CF.Exists {CF.formula_exists_qvars = svs; CF.formula_exists_heap = h; 
               CF.formula_exists_pure = p; CF.formula_exists_label = b} ->  
    "(exists " ^ (string_of_elems svs fixbag_of_spec_var ",") ^ ": " ^ 
    fixbag_of_h_formula h ^ op_and ^ fixbag_of_mix_formula (p,b) ^ ")"

let fixbag = "fixbag4"

let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let todo_unk = Unix.close_process (ic, oc) in
  (Buffer.contents buf)


let rec remove_paren s n = if n=0 then "" else match s.[0] with
    | '(' -> remove_paren (String.sub s 1 (n-1)) (n-1)
    | ')' -> remove_paren (String.sub s 1 (n-1)) (n-1)
    | _ -> (String.sub s 0 1) ^ (remove_paren (String.sub s 1 (n-1)) (n-1))

let compute_inv name vars fml pf no_of_disjs =
  if not !Globals.do_infer_inv then pf
  else
    let rhs = string_of_elems fml (fun (c,_) ->fixbag_of_formula c) op_or in
    let no = string_of_int no_of_disjs in
    let input_fixbag = 
      try
        name ^ "(" ^"self," ^ (string_of_elems vars fixbag_of_spec_var ",") ^ " -> "
        ^ res_name ^ ") := " 
        ^ rhs
      with _ -> report_error no_pos "Error in translating the input for fixbag"
    in
    (*print_endline ("\nINPUT: " ^ input_fixbag);*)
    DD.info_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
    DD.info_zprint (lazy (("Input of fixbag: " ^ input_fixbag))) no_pos;
    (*      let output_of_sleek = "fixbag.inf" in*)
    (*      let oc = open_out output_of_sleek in*)
    (*      Printf.fprintf oc "%s" input_fixbag;*)
    (*      flush oc;*)
    (*      close_out oc;*)
    let res = syscall (fixbag ^ " \'" ^ input_fixbag ^ "\' \'" ^ no ^ "\'") in
    let res = remove_paren res (String.length res) in
    (*print_endline ("RES: " ^ res);*)
    DD.info_zprint (lazy (("Result of fixbag: " ^ res))) no_pos;
    let new_pf = List.hd (Parse_fixbag.parse_fix res) in
    let () = x_dinfo_hp (add_str "Result of fixbag (parsed): "  !CP.print_formula) new_pf no_pos in
    let check_imply = Omega.imply new_pf pf "1" 100.0 in
    if check_imply then (
      Pr.fmt_string "INV:  ";
      Pr.pr_angle name (fun x -> Pr.fmt_string (Pr.string_of_typed_spec_var x)) vars;
      Pr.fmt_string ("\nOLD: " ^ (Pr.string_of_pure_formula pf) ^
                     "\nNEW: " ^ (Pr.string_of_pure_formula new_pf) ^ "\n\n");			
      new_pf)
    else pf


(*let compute_fixpoint input_pairs =
  let (pfs, rels) = List.split input_pairs in
  let rels = Gen.BList.remove_dups_eq CP.equalFormula rels in
  let rel_fml = match rels with
    | [] -> report_error no_pos "Error in compute_fixpoint"
    | [hd] -> hd
    | _ -> report_error no_pos "Fixbag.ml: More than one input relation"
  in
  let (name,vars) = match rel_fml with
    | CP.BForm ((CP.RelForm (name,args,_),_),_) -> (CP.name_of_spec_var name, (List.concat (List.map CP.afv args)))
    | _ -> report_error no_pos "Wrong format"
  in
  let pf = List.fold_left (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (List.hd pfs) (List.tl pfs) in  
  try
    let rhs = fixbag_of_pure_formula pf in 
    let input_fixbag =  name ^ ":={[" ^ (string_of_elems vars fixbag_of_spec_var ",") 
      ^ "] -> [] -> []: " ^ rhs ^ "\n};\n\nFix1:=bottomup(" ^ name ^ ",1,SimHeur);\nFix1;\n"
      ^ "Fix2:=topdown(" ^ name ^ ",1,SimHeur);\nFix2;"
    in
    (*print_endline ("\nINPUT: " ^ input_fixbag);*)
    x_tinfo_hp (add_str "input_pairs: " (pr_list (pr_pair !CP.print_formula !CP.print_formula))) input_pairs no_pos;
    x_dinfo_pp ">>>>>> compute_fixpoint <<<<<<" no_pos;
    x_dinfo_pp ("Input of fixbag: " ^ input_fixbag) no_pos;
    let output_of_sleek = "fixbag.inf" in
    let oc = open_out output_of_sleek in
    Printf.fprintf oc "%s" input_fixbag;
    flush oc;
    close_out oc;
    let res = syscall (fixbag ^ " " ^ output_of_sleek) in
    let res = remove_paren res (String.length res) in
    (*print_endline ("RES: " ^ res);*)
    x_dinfo_pp ("Result of fixbag: " ^ res) no_pos;
    let fixpoint = Parse_fix.parse_fix res in
    x_dinfo_hp (add_str "Result of fixbag (parsed): " (pr_list !CP.print_formula)) fixpoint no_pos;
    let fixpoint = List.map (fun f -> 
        let args = CP.fv f in 
        let quan_vars = CP.diff_svl args vars in
        TP.simplify_raw (CP.mkExists quan_vars f None no_pos)) fixpoint in
    match fixpoint with
      | [pre;post] -> (rel_fml, pre, post)
      | _ -> report_error no_pos "Expecting a pair of pre-post"
  with _ -> report_error no_pos "Unexpected error in computing fixpoint"*)

let rec is_rec pf = match pf with
  | CP.BForm (bf,_) -> CP.is_RelForm pf
  | CP.And (f1,f2,_) -> is_rec f1 || is_rec f2
  | CP.AndList b -> exists_l_snd is_rec b
  | CP.Or (f1,f2,_,_) -> is_rec f1 || is_rec f2
  | CP.Not (f,_,_) -> is_rec f
  | CP.Forall (_,f,_,_) -> is_rec f
  | CP.Exists (_,f,_,_) -> is_rec f

let rec get_rel_vars pf = match pf with
  | CP.BForm (bf,_) -> if CP.is_RelForm pf then CP.get_rel_args pf else []
  | CP.And (f1,f2,_) -> get_rel_vars f1 @ get_rel_vars f2
  | CP.AndList b -> fold_l_snd get_rel_vars b
  | CP.Or (f1,f2,_,_) -> get_rel_vars f1 @ get_rel_vars f2
  | CP.Not (f,_,_) -> get_rel_vars f
  | CP.Forall (_,f,_,_) -> get_rel_vars f
  | CP.Exists (_,f,_,_) -> get_rel_vars f

let substitute (e: CP.exp): (CP.exp * CP.formula list) = match e with
  | CP.Var _ -> (e, [])
  | _ -> (
      try 
        let arb = List.hd (CP.afv e) in 
        let var = CP.fresh_spec_var_prefix "fb" arb in
        let var = CP.mkVar var no_pos in
        (var, [CP.mkEqExp var e no_pos])
      with _ -> (e,[]))

let arr_para_order (rel: CP.formula) (rel_def: CP.formula) (ante_vars: CP.spec_var list) = match (rel,rel_def) with
  | (CP.BForm ((CP.RelForm (id,args,p), o1), o2), CP.BForm ((CP.RelForm (id_def,args_def,_), _), _)) -> 
    if id = id_def then 
      let new_args_def = 
        let pre_args, post_args = List.partition (fun e -> Gen.BList.subset_eq CP.eq_spec_var (CP.afv e) ante_vars) args_def in
        pre_args @ post_args 
      in
      let pairs = List.combine args_def args in
      let new_args = List.map (fun a -> List.assoc a pairs) new_args_def in
      let new_args, subs = List.split (List.map (fun a -> substitute a) new_args) in
      let id = match id with | CP.SpecVar (t,n,p) -> CP.SpecVar (t,"fixbagA"(* ^ n*),p) in
      (CP.BForm ((CP.RelForm (id,new_args,p), o1), o2), [CP.conj_of_list (List.concat subs) no_pos])
    else 
      let args, subs = List.split (List.map (fun a -> substitute a) args) in
      let id = match id with | CP.SpecVar (t,n,p) -> CP.SpecVar (t,"fixbagA"(* ^ n*),p) in
      (CP.BForm ((CP.RelForm (id,args,p), o1), o2), [CP.conj_of_list (List.concat subs) no_pos])
  | _ -> report_error no_pos "Expecting relation formulae"

(*let arr_args rcase_orig rel ante_vars = *)
(*  let rels = CP.get_RelForm rcase_orig in*)
(*  let rels,lp = List.split (List.map (fun r -> arr_para_order r rel ante_vars) rels) in*)
(*  let rcase = TP.simplify_raw (CP.drop_rel_formula rcase_orig) in*)
(*  CP.conj_of_list ([rcase]@rels@(List.concat lp)) no_pos*)

(*let propagate_exp exp1 exp2 = match (exp1, exp2) with (* Need to cover all patterns *)*)
(*  | (CP.Lte(e1, CP.IConst(i2, _), _), CP.Lte(e3, CP.IConst(i4, _), _)) ->*)
(*    if CP.eqExp e1 e3 && i2 > i4 then Some (CP.Lte(e1, CP.IConst(i4, no_pos), no_pos)) else None*)
(*  | (CP.Lte(e1, CP.IConst(i2, _), _), CP.Eq(e3, CP.IConst(i4, _), _))*)
(*  | (CP.Lte(e1, CP.IConst(i2, _), _), CP.Eq(CP.IConst(i4, _), e3, _)) ->*)
(*    if CP.eqExp e1 e3 && i2 > i4 then Some (CP.Lte(e1, CP.IConst(i4, no_pos), no_pos)) else None*)
(*  | (CP.Lte(CP.IConst(i2, _), e1, _), CP.Eq(e3, CP.IConst(i4, _), _))*)
(*  | (CP.Lte(CP.IConst(i2, _), e1, _), CP.Eq(CP.IConst(i4, _), e3, _)) ->*)
(*    if CP.eqExp e1 e3 && i2 < i4 then Some (CP.Gte(e1, CP.IConst(i4, no_pos), no_pos)) else None*)
(*  | (CP.Lte(e1, CP.IConst(i2, _), _), CP.Lt(e3, CP.IConst(i4, _), _)) ->*)
(*    if CP.eqExp e1 e3 && i2 >= i4 then Some (CP.Lt(e1, CP.IConst(i4, no_pos), no_pos)) else None*)
(*  | (CP.Gte(e1, CP.IConst(i2, _), _), CP.Gte(e3, CP.IConst(i4, _), _)) ->*)
(*    if CP.eqExp e1 e3 && i2 < i4 then Some (CP.Gte(e1, CP.IConst(i4, no_pos), no_pos)) else None*)
(*  | (CP.Gte(e1, CP.IConst(i2, _), _), CP.Eq(e3, CP.IConst(i4, _), _))*)
(*  | (CP.Gte(e1, CP.IConst(i2, _), _), CP.Eq(CP.IConst(i4, _), e3, _)) ->*)
(*    if CP.eqExp e1 e3 && i2 < i4 then Some (CP.Gte(e1, CP.IConst(i4, no_pos), no_pos)) else None*)
(*  | (CP.Gte(e1, CP.IConst(i2, _), _), CP.Gt(e3, CP.IConst(i4, _), _)) ->*)
(*    if CP.eqExp e1 e3 && i2 <= i4 then Some (CP.Gt(e1, CP.IConst(i4, no_pos), no_pos)) else None*)
(*  | _ -> None  *)

(*let propagate_exp exp1 exp2 = *)
(*  let pr0 = !CP.print_p_formula in*)
(*  Debug.no_2 "propagate_exp" pr0 pr0 (pr_option pr0)*)
(*      (fun _ _ -> propagate_exp exp1 exp2) exp1 exp2*)

(*let propagate_fml rcase bcase = match (rcase, bcase) with*)
(*  | (CP.BForm ((exp1,_),_), CP.BForm ((exp2,_),_)) -> *)
(*    let exp = propagate_exp exp1 exp2 in*)
(*    (match exp with*)
(*    | None -> []*)
(*    | Some e -> [CP.BForm ((e,None),None)])*)
(*  | _ -> []*)

(*let propagate_fml rcase bcase = *)
(*  let pr0 = !CP.print_formula in*)
(*  Debug.no_2 "propagate_fml" pr0 pr0 (pr_list pr0)*)
(*      (fun _ _ -> propagate_fml rcase bcase) rcase bcase*)

let matching_exp pf1 pf2 = match (pf1,pf2) with
  | (Lt (Var (v1,p1), Var (v2,p2), p), Lt (Var (v3,_), Var (v4,_), _))
  | (Gt (Var (v1,p1), Var (v2,p2), p), Gt (Var (v3,_), Var (v4,_), _)) -> 
    let res = eq_spec_var v1 v4 && eq_spec_var v2 v3 in
    if res then (true, [Neq  (Var (v1,p1), Var (v2,p2), p)]) else (false,[])
  | (Eq (v1, Bag ([],_), _), Eq (v2, BagUnion (es,_), _))
  | (Eq (v1, Bag ([],_), _), Eq (BagUnion (es,_), v2, _))
  | (Eq (Bag ([],_), v1, _), Eq (v2, BagUnion (es,_), _))
  | (Eq (Bag ([],_), v1, _), Eq (BagUnion (es,_), v2, _))
  | (Eq (v2, BagUnion (es,_), _), Eq (v1, Bag ([],_), _)) 
  | (Eq (v2, BagUnion (es,_), _), Eq (Bag ([],_), v1, _)) 
  | (Eq (BagUnion (es,_), v2, _), Eq (v1, Bag ([],_), _)) 
  | (Eq (BagUnion (es,_), v2, _), Eq (Bag ([],_), v1, _)) -> 
    begin
      match (v1,v2) with
      | (Var (b1,_), Var (b2,_))
        (*      | (Subtract (_, Subtract (_,Var (b1,_),_),_), Var (b2,_))*)
        (*      | (Var (b1,_), Subtract (_, Subtract (_,Var (b2,_),_),_))*)
        (*      | (Subtract (_, Subtract (_,Var (b1,_),_),_), Subtract (_, Subtract (_,Var (b2,_),_),_))*)
        -> (eq_spec_var b1 b2 && es != [],[])
      | _ -> (false,[])
    end
  | _ -> (false,[])

let matching f1 f2 = match (f1,f2) with
  | (BForm ((pf1,o),p), BForm ((pf2,_),_)) -> 
    (*    x_dinfo_hp (add_str "matching: " (pr_list !CP.print_formula)) [f1;f2] no_pos;*)
    let (res1,res2) = matching_exp pf1 pf2 in
    if res2 = [] then (res1,[])
    else (res1,List.map (fun r2 -> BForm((r2,o),p)) res2)
  | _ -> (false,[])

let can_merge f1 f2 =
  let conjs1 = CP.list_of_conjs f1 in
  let conjs2 = CP.list_of_conjs f2 in
  (*    x_dinfo_hp (add_str "CONJ1: " (pr_list !CP.print_formula)) conjs1 no_pos;*)
  (*    x_dinfo_hp (add_str "CONJ2: " (pr_list !CP.print_formula)) conjs2 no_pos;*)
  let part_of_f1, others1 = List.partition (fun c -> Gen.BList.mem_eq (CP.equalFormula) c conjs1) conjs2 in
  (*x_dinfo_hp (add_str "PART1: " (pr_list !CP.print_formula)) part_of_f1 no_pos;*)
  (*x_dinfo_hp (add_str "other1: " (pr_list !CP.print_formula)) others1 no_pos;*)
  let part_of_f2, others2 = List.partition (fun c -> Gen.BList.mem_eq (CP.equalFormula) c conjs2) conjs1 in
  (*x_dinfo_hp (add_str "PART2: " (pr_list !CP.print_formula)) part_of_f2 no_pos;*)
  (*x_dinfo_hp (add_str "other2: " (pr_list !CP.print_formula)) others2 no_pos;*)
  let check1 = List.length part_of_f1 = List.length part_of_f2 && List.length others1 = List.length others2 in
  (* TODO: *)
  let matching = if check1 then List.map2 (fun o1 o2 -> matching o1 o2) others1 others2 else [] in
  let added_conj = List.concat (List.map (fun (f1,f2) -> if f1 then f2 else []) matching) in
  let check = check1 && List.for_all fst matching in
  if check then (true, conj_of_list (part_of_f1@added_conj) no_pos)
  else (false, f1)

let rec simplify flist = match flist with
  | [] -> []
  | [hd] -> [hd]
  | hd::tl ->
    let check_merge = List.map (fun f -> can_merge f hd) tl in
    let (can_merge, others) = List.partition fst check_merge in
    (*    x_dinfo_hp (add_str "MERGE: " (pr_list !CP.print_formula)) (snd (List.split can_merge)) no_pos;*)
    (*    x_dinfo_hp (add_str "OTHER: " (pr_list !CP.print_formula)) (snd (List.split others)) no_pos;*)
    if can_merge = [] then hd::(simplify tl)
    else
      (* TODO: *)
      let hd = snd (List.hd (List.rev can_merge)) in
      hd::(simplify (snd (List.split others)))

let pre_process vars fmls =
  List.filter (fun f ->
      let vs = List.filter (fun x -> CP.is_bag_typ x || CP.is_bool_typ x) (CP.fv f) in
      (*    x_dinfo_hp (add_str "VARS: " !print_svl) vs no_pos;*)
      CP.subset vs vars) fmls

let rec create_alias_tbl vs aset all_rel_vars base_case = match vs with
  | [] -> []
  | [hd] -> 
    if base_case then 
      [hd::(List.filter (fun x -> not(List.mem x all_rel_vars)) (CP.EMapSV.find_equiv_all hd aset))]
    else [List.filter (fun x -> not(List.mem x all_rel_vars)) (hd::(CP.EMapSV.find_equiv_all hd aset))]
  | hd::tl ->
    let res1 = create_alias_tbl [hd] aset all_rel_vars base_case in
    let tl = List.filter (fun x -> not(List.mem x (List.hd res1))) tl in
    res1@(create_alias_tbl tl aset all_rel_vars base_case)

let rewrite pure rel_lhs_vars rel_vars base_case =
  let als = MCP.ptr_bag_equations_without_null (MCP.mix_of_pure pure) in
  (*  DD.info_hprint (add_str "ALS: " (pr_list (pr_pair !print_sv !print_sv))) als no_pos;*)
  let aset = CP.EMapSV.build_eset als in
  let int_vars, other_vars = List.partition CP.is_int_typ (CP.fv pure) in
  let alias = create_alias_tbl (rel_vars@int_vars@other_vars) aset rel_lhs_vars base_case in
  let subst_lst = List.concat (List.map (fun vars -> if vars = [] then [] else 
                                            let hd = List.hd vars in List.map (fun v -> (v,hd)) (List.tl vars)) alias) in
  (*  DD.info_hprint (add_str "SUBS: " (pr_list (pr_pair !print_sv !print_sv))) subst_lst no_pos;*)
  (*  DD.info_hprint (add_str "PURE: " (!CP.print_formula)) pure no_pos;*)
  let pure = CP.subst subst_lst pure in
  CP.remove_redundant_constraints pure

(*let rewrite2 pure rel_lhs_vars rel_vars =*)
(*  let als = MCP.ptr_bag_equations_without_null (MCP.mix_of_pure pure) in*)
(*  let aset = CP.EMapSV.build_eset als in*)
(*  let pure_vars = CP.fv pure in*)
(*  let int_vars, other_vars = List.partition CP.is_int_typ pure_vars in*)
(*  let alias = create_alias_tbl (rel_vars@int_vars@other_vars) aset rel_lhs_vars in*)
(*  let subst_lst = List.concat (List.map (fun vars -> if vars = [] then [] else *)
(*      let hd = List.hd vars in *)
(*        List.concat (List.map (fun v -> *)
(*          if mem_svl v pure_vars && mem_svl hd pure_vars then [mkEqVar v hd no_pos] else []) *)
(*        (List.tl vars))) alias) in*)
(*(*  DD.info_hprint (add_str "PURE: " (!CP.print_formula)) pure no_pos;*)*)
(*  let pure = conj_of_list (pure::subst_lst) no_pos in*)
(*  CP.remove_dup_constraints pure*)

let rec get_all_pairs conjs = match conjs with
  | [] -> []
  | c::cs -> 
    let lst = List.map (fun conj -> (c,conj)) cs in
    lst @ (get_all_pairs cs)

let rec rewrite_by_subst pairs = match pairs with
  | [] -> []
  | [(e1,e2)] ->
    begin
      match (e1,e2) with
      | (BForm ((pf1,_),_), BForm ((pf2,_),_)) -> 
        begin
          match pf1,pf2 with
          | Eq (exp1, exp2, _), Eq (exp3, exp4, _) ->
            begin
              match (exp1,exp2,exp3,exp4) with 
              (* Add more if necessary *)
              | Var (sv11,_), BagUnion ([Var (sv12,_);Bag([Var (sv13,_)],_)],_), 
                Var (sv21,_), BagUnion ([BagUnion ([Var (sv22,_);Bag([Var (sv23,_)],_)],_); 
                                         Bag([Var (sv24,_)],_)],_)
              (*        | Var (sv11,_), BagUnion ([Var (sv12,_);Bag([Var (sv13,_)],_)],_), *)
              (*          Var (sv21,_), BagUnion ([Subtract (_,Subtract(_,BagUnion ([Var (sv22,_);*)
              (*          Bag([Var (sv23,_)],_)],_),_),_); Bag([Var (sv24,_)],_)],_) *)
              | Var (sv21,_), BagUnion ([BagUnion ([Var (sv22,_);Bag([Var (sv23,_)],_)],_); 
                                         Bag([Var (sv24,_)],_)],_), 
                Var (sv11,_), BagUnion ([Var (sv12,_);Bag([Var (sv13,_)],_)],_)
                (*        | Var (sv21,_), BagUnion ([Subtract (_,Subtract(_,BagUnion ([Var (sv22,_);*)
                (*          Bag([Var (sv23,_)],_)],_),_),_); Bag([Var (sv24,_)],_)],_), *)
                (*          Var (sv11,_), BagUnion ([Var (sv12,_);Bag([Var (sv13,_)],_)],_)*)
                ->
                if eq_spec_var sv12 sv22 && eq_spec_var sv13 sv23 then
                  [CP.mkEqExp (mkVar sv21 no_pos) (BagUnion ([mkVar sv11 no_pos; Bag([mkVar sv24 no_pos],no_pos)],no_pos)) no_pos]
                else []
              | Var (sv11,_), BagUnion ([Var (sv12,_);Var (sv13,_);Bag([Var (sv14,_)],_)],_), 
                Var (sv21,_), BagUnion ([Var (sv22,_);Var (sv23,_);Bag([Var (sv24,_)],_)],_)
                -> 
                if eq_spec_var sv13 sv23 && eq_spec_var sv14 sv24 then
                  [CP.mkEqExp (mkVar sv21 no_pos) (BagUnion ([mkVar sv22 no_pos; 
                                                              Bag([mkVar (SpecVar (Int,"v_fb",Unprimed)) no_pos],no_pos)],no_pos)) no_pos;
                   CP.mkEqExp (mkVar sv11 no_pos) (BagUnion ([mkVar sv12 no_pos; 
                                                              Bag([mkVar (SpecVar (Int,"v_fb",Unprimed)) no_pos],no_pos)],no_pos)) no_pos]
                else []
              | _ -> []
            end
          | _ -> []
        end
      | _ -> []
    end
  | p::ps -> (rewrite_by_subst [p]) @ (rewrite_by_subst ps)

let rec rewrite_by_subst2 pairs = match pairs with
  | [] -> []
  | [(f1,f2)] ->
    begin
      match (f1,f2) with
      | (BForm ((Eq (exp1, exp2, _),_),_), BForm ((Eq (exp3, exp4, _),_),_)) -> 
        begin
          match (exp1,exp2,exp3,exp4) with 
          | Var (sv1,_), Var (sv2,_), Var (sv3,_), BagUnion (es,_) -> 
            let evars = List.concat (List.map afv es) in
            let subst = 
              if mem_svl sv3 evars && eq_spec_var sv1 sv3 && is_bag_typ sv1 then [(sv1,sv2)] else
              if mem_svl sv3 evars && eq_spec_var sv2 sv3 && is_bag_typ sv1 then [(sv2,sv1)] else [] in
            let exp = e_apply_subs subst exp4 in
            if subst = [] then [] else [([f1;f2],[CP.mkEqExp (mkVar sv3 no_pos) exp no_pos])]
          | _ -> []
        end
      | (Forall _, Forall _) -> [([f1;f2],[])]
      | (Forall _,_) -> [([f1],[])]
      | (_,Forall _) -> [([f2],[])]
      | _ -> []
    end
  | p::ps -> (rewrite_by_subst2 [p]) @ (rewrite_by_subst2 ps)

let rec filter_var f vars = 
  match f with
  | CP.Or (f1,f2,l,p) -> CP.mkOr (filter_var f1 vars) (filter_var f2 vars) l p
  | _ -> CP.filter_var (CP.drop_rel_formula f) vars

let propagate_rec_helper rcase_orig rel ante_vars =
  let rel_vars = CP.remove_dups_svl (get_rel_vars rcase_orig) in
  (*  x_dinfo_hp (add_str "Before: " (!CP.print_formula)) rcase_orig no_pos;*)
  (*  let rcase = TP.simplify_raw (CP.drop_rel_formula rcase_orig) in*)
  (*  x_dinfo_hp (add_str "After: " (!CP.print_formula)) rcase no_pos;*)
  let rcase = CP.drop_rel_formula rcase_orig in
  let rel_lhs_vars = CP.fv rel in
  let all_rel_vars = rel_vars @ rel_lhs_vars in
  let rcase = filter_var rcase all_rel_vars in
  (*  x_dinfo_hp (add_str "RCASE: " (!CP.print_formula)) rcase no_pos;*)
  let rcase = rewrite rcase rel_lhs_vars rel_vars false in
  (*  x_dinfo_hp (add_str "RCASE: " (!CP.print_formula)) rcase no_pos;*)
  (*  let all_rel_vars = rel_vars @ (CP.fv rel) in*)
  (*  let als = MCP.ptr_bag_equations_without_null (MCP.mix_of_pure rcase) in*)
  (*  let aset = CP.EMapSV.build_eset als in*)
  (*  let other_vars = List.filter (fun x -> CP.is_int_typ x) (CP.fv rcase_orig) in*)
  (*  let alias = create_alias_tbl (rel_vars@other_vars) aset (CP.fv rel) in*)
  (*  let subst_lst = List.concat (List.map (fun vars -> if vars = [] then [] else *)
  (*      let hd = List.hd vars in List.map (fun v -> (v,hd)) (List.tl vars)) alias) in*)
  (*(*  x_dinfo_hp (add_str "SUBS: " (pr_list (pr_pair !print_sv !print_sv))) subst_lst no_pos;*)*)
  (*(*  x_dinfo_hp (add_str "RCASE: " (!CP.print_formula)) rcase no_pos;*)*)
  (*  let rcase = CP.subst subst_lst rcase in*)
  (*  let rcase = MCP.remove_ptr_equations rcase false in*)
  let rcase_conjs = CP.list_of_conjs rcase in
  if List.exists (fun conj -> is_emp_bag conj rel_vars) rcase_conjs then CP.mkFalse no_pos
  else
    let rcase_conjs_eq = List.filter is_beq_exp rcase_conjs in
    let rcase_conjs = 
      if List.length rcase_conjs_eq <= 4 then
        let all_pairs = get_all_pairs rcase_conjs_eq in
        (*        DD.info_hprint (add_str "PAIRS: " (pr_list (pr_pair !CP.print_formula !CP.print_formula))) all_pairs no_pos;*)
        rcase_conjs @ (rewrite_by_subst all_pairs)
      else rcase_conjs 
    in
    let rcase = CP.conj_of_list (pre_process all_rel_vars rcase_conjs) no_pos in
    let rcase = filter_var rcase all_rel_vars in
    (*    x_dinfo_hp (add_str "RCASE: " (!CP.print_formula)) rcase no_pos;*)
    let rcase = if CP.diff_svl (List.filter is_bag_typ rel_vars) (CP.fv rcase) != [] then CP.mkFalse no_pos else rcase in
    let rels = CP.get_RelForm rcase_orig in
    let rels,lp = List.split (List.map (fun r -> arr_para_order r rel ante_vars) rels) in
    (*  let exists_vars = CP.diff_svl (CP.fv rcase) rel_vars in*)
    (*  let rcase2 = TP.simplify_raw (CP.mkExists exists_vars rcase None no_pos) in*)
    CP.conj_of_list ([rcase]@rels@(List.concat lp)) no_pos
(*  try*)
(*    let pairs = List.combine (CP.fv rel) rel_vars in*)
(*    let bcase = CP.subst pairs bcase_orig in*)
(*    let pf = List.concat (List.map (fun b -> List.concat *)
(*        (List.map (fun r -> propagate_fml r b) (CP.list_of_conjs rcase2))) (CP.list_of_conjs bcase)) in*)
(*    CP.conj_of_list ([rcase]@rels@pf@(List.concat lp)) no_pos*)
(*  (*  print_endline ("PURE: " ^ Cprinter.string_of_pure_formula rcase);*)*)
(*  (*  print_endline ("PURE2: " ^ Cprinter.string_of_pure_formula bcase);*)*)
(*  (*  print_endline ("PURE3: " ^ Cprinter.string_of_pure_formula pf);*)*)
(*  with _ -> rcase_orig*)

(*let rec remove_weaker_bcase bcases = match bcases with
  | [] -> []
  | b::bs ->
    if List.exists (fun fml -> TP.imply_raw fml b) bs then remove_weaker_bcase bs
    else
      b::(remove_weaker_bcase (List.filter (fun fml -> not(TP.imply_raw b fml)) bs))*)

(* TODO: Need to handle computed relation in the future *)
(*let rec get_other_branches or_fml args = match or_fml with*)
(*  | Or fml -> *)
(*    (get_other_branches fml.formula_or_f1 args) @ (get_other_branches fml.formula_or_f2 args)*)
(*  | _ ->*)
(*    let _,p,_,_,_ = split_components or_fml in*)
(*    let conjs = CP.list_of_conjs (MCP.pure_of_mix p) in*)
(*    List.filter (fun pure -> CP.subset args (CP.fv pure)) conjs*)

let rec transform fml v_synch fv_rel = match fml with
  | BForm ((Eq (v1, BagUnion ([b2;Bag([Var (v,_)],_)],_), _), _),_)
  | BForm ((Eq (v1, BagUnion ([Bag([Var (v,_)],_);b2],_), _), _),_)
  | BForm ((Eq (BagUnion ([Bag([Var (v,_)],_);b2],_), v1, _), _),_)
  | BForm ((Eq (BagUnion ([b2;Bag([Var (v,_)],_)],_), v1, _), _),_) -> 
    begin
      match v1 with
      | Var (b1,_) ->
        if diff_svl (CP.fv fml) fv_rel = [] then
          let vars = afv b2 in
          let v_synch = List.filter (fun x -> not (eq_spec_var x v)) v_synch in
          begin
            match (vars,v_synch) with
            | ([hd],[v_s]) ->
              let v_new = v_s in
              let b2_new = CP.fresh_spec_var_prefix "FB" hd in
              let als1 = CP.mkEqVar v v_new no_pos in
              let als2 = CP.mkEqVar hd b2_new no_pos in
              let f_new = mkEqExp (mkVar b1 no_pos) (BagUnion([mkVar b2_new no_pos;Bag([mkVar v_new no_pos],no_pos)],no_pos)) no_pos in
              conj_of_list [als1;als2;f_new] no_pos
            | _ -> fml
          end
        else fml
      | _ -> fml
    end
  | And (BForm f1, BForm f2, _) -> mkAnd (transform (BForm f1) v_synch fv_rel) (transform (BForm f2) v_synch fv_rel) no_pos
  | And _ -> 
    let v_synch = List.filter CP.is_int_typ (CP.diff_svl v_synch fv_rel) in
    let v_subst = List.filter CP.is_int_typ (CP.diff_svl (CP.fv fml) fv_rel) in
    (*    x_dinfo_hp (add_str "VSYNCH: " (!print_svl)) v_synch no_pos;*)
    (*    x_dinfo_hp (add_str "VSUBST: " (!print_svl)) v_subst no_pos;*)
    (match (v_subst, v_synch) with
     | ([hd],[v_s]) -> CP.subst [(hd,v_s)] fml
     | _ -> fml
    )
  | _ -> fml

let rec remove_subtract_exp e = match e with
  | CP.Subtract (_, Subtract (_,en,_), _) -> remove_subtract_exp en
  | CP.Bag (es, p) -> Bag (List.map remove_subtract_exp es, p)
  | CP.BagUnion (es, p) -> BagUnion (List.map remove_subtract_exp es, p)
  | CP.BagIntersect (es, p) -> BagIntersect (List.map remove_subtract_exp es, p)
  | CP.BagDiff (e1, e2, p) -> BagDiff (remove_subtract_exp e1, remove_subtract_exp e2, p)
  | _ -> e

let remove_subtract_pf pf = match pf with
  | CP.Lt (e1, e2, p) -> Lt(remove_subtract_exp e1, remove_subtract_exp e2, p)
  | CP.Lte (e1, e2, p) -> Lte(remove_subtract_exp e1, remove_subtract_exp e2, p)
  | CP.Gt (e1, e2, p) -> Gt(remove_subtract_exp e1, remove_subtract_exp e2, p)
  | CP.Gte (e1, e2, p) -> Gte(remove_subtract_exp e1, remove_subtract_exp e2, p)
  | CP.Eq (e1, e2, p) -> Eq(remove_subtract_exp e1, remove_subtract_exp e2, p)
  | CP.Neq (e1, e2, p) -> Neq(remove_subtract_exp e1, remove_subtract_exp e2, p)
  | _ -> pf

let rec remove_subtract pure = match pure with
  | BForm ((pf,o1),o2) -> BForm ((remove_subtract_pf pf,o1),o2)
  | And (f1,f2,_) -> CP.mkAnd (remove_subtract f1) (remove_subtract f2) no_pos
  | Or (f1,f2,_,_) -> CP.mkOr (remove_subtract f1) (remove_subtract f2) None no_pos
  | Not (f,_,_) -> CP.mkNot_s (remove_subtract f)
  | Forall (v,f,o,p) -> Forall (v,remove_subtract f,o,p)
  | Exists (v,f,o,p) -> Exists (v,remove_subtract f,o,p)
  | AndList l -> AndList (map_l_snd remove_subtract l)

let isComp pure = match pure with
  | BForm ((pf,_),_) ->
    begin
      match pf with
      | Lt _ | Gt _ | Lte _ | Gte _ -> true
      | _ -> false
    end
  | _ -> false

let propagate_rec pfs rel ante_vars = match CP.get_rel_id rel with
  | None -> (pfs,1)
  | Some ivs ->
    let (rcases, bcases) = List.partition is_rec pfs in
    (*    let or_post = get_or_post specs (CP.get_rel_id_list rel) in*)
    (*    let bcases = *)
    (*      begin*)
    (*      match or_post with*)
    (*      | [] -> bcases*)
    (*      | [or_fml] ->*)
    (*        let other_branches = get_other_branches or_fml (CP.get_rel_args rel) in*)
    (*        let other_branches = List.map (fun p -> CP.mkNot_s p) other_branches in*)
    (*        let pure_other_branches = CP.conj_of_list other_branches no_pos in*)
    (*        List.filter (fun b -> TP.is_sat_raw (CP.mkAnd b pure_other_branches no_pos)) bcases*)
    (*      | _ -> bcases*)
    (*      end*)
    (*    in*)
    (*    let no_of_disjs = List.map (fun b -> let disjs = CP.list_of_disjs b in*)
    (*        let cond = List.exists (fun d -> let conjs = CP.list_of_conjs d in*)
    (*            List.exists (fun c -> CP.is_eq_const c) conjs) disjs in*)
    (*        if cond then 1 else List.length disjs) bcases in*)
    (*    (*let no_of_disjs = List.map (fun b -> CP.no_of_disjs b) bcases in*)*)
    (*    let no_of_disjs = List.fold_left (fun a b -> max a b) 1 no_of_disjs in*)
    let bcases = List.concat (List.map (fun x -> CP.list_of_disjs x) bcases) in
    let rcases = List.concat (List.map (fun x -> CP.list_of_disjs (TP.simplify_raw x)) rcases) in
    let bcases = List.map remove_subtract bcases in
    let bcases = List.map (fun bcase -> 
        let conjs = list_of_conjs bcase in
        let conjs =  Gen.BList.remove_dups_eq CP.equalFormula (List.filter (fun x -> not (isComp x)) conjs) in
        conj_of_list conjs no_pos) bcases in
    let rcases = List.map remove_subtract rcases in
    x_dinfo_hp (add_str "BCASE: " (pr_list !CP.print_formula)) bcases no_pos;
    let bcases = simplify bcases in
    (*    x_dinfo_hp (add_str "BCASE: " (pr_list !CP.print_formula)) bcases no_pos;*)
    (*    x_dinfo_hp (add_str "RCASE: " (pr_list !CP.print_formula)) rcases no_pos;*)
    let rcases = simplify rcases in
    x_dinfo_hp (add_str "RCASE: " (pr_list !CP.print_formula)) rcases no_pos;
    let rcases = List.map (fun rcase -> propagate_rec_helper rcase rel ante_vars) rcases in
    x_dinfo_hp (add_str "RCASE: " (pr_list !CP.print_formula)) rcases no_pos;
    let fv_rel = get_rel_args rel in
    let bcases = List.map (fun x -> let fv_x = CP.fv x in
                            if List.length fv_x <= 10 || !dis_ps (* not(!allow_pred_spec) *) then x else
                              let r = CP.mkExists (CP.diff_svl (CP.fv x) fv_rel) x None no_pos in 
                              let r = Redlog.elim_exists_with_eq r in
                              TP.simplify_raw r) bcases in
    (*    let bcases = List.map (fun x -> rewrite2 x [] fv_rel) bcases in*)
    let bcases = List.map remove_subtract bcases in
    let bcases = List.map (fun x -> rewrite x fv_rel [] true) bcases in
    let bcases = List.map (fun x -> rewrite x fv_rel [] true) bcases in
    (*    x_dinfo_hp (add_str "BCASE: " (pr_list !CP.print_formula)) bcases no_pos;*)
    let bcases = List.map (fun x -> CP.remove_cnts2 fv_rel x) bcases in
    let v_synch = List.filter is_int_typ (List.concat (List.map fv rcases)) in
    (*    x_dinfo_hp (add_str "BCASE: " (pr_list !CP.print_formula)) bcases no_pos;*)
    let bcases = List.map (fun x -> transform x v_synch fv_rel) bcases in
    x_dinfo_hp (add_str "BCASE: " (pr_list !CP.print_formula)) bcases no_pos;
    let bcases = Gen.BList.remove_dups_eq (fun p1 p2 -> TP.imply_raw p1 p2 && TP.imply_raw p2 p1) bcases in
    let bcases = if List.length fv_rel <= 5 then bcases else
        List.map (fun bcase -> 
            let bcase = remove_subtract bcase in
            let bcase_conjs = list_of_conjs bcase in
            let all_pairs = get_all_pairs bcase_conjs in
            (*        DD.info_hprint (add_str "PAIRS: " (pr_list (pr_pair !CP.print_formula !CP.print_formula))) all_pairs no_pos;*)
            let (rem,add) = List.split (rewrite_by_subst2 all_pairs) in
            let conjs = (Gen.BList.difference_eq (=) bcase_conjs (List.concat rem)) @ (List.concat add) in
            conj_of_list conjs no_pos
          ) bcases 
    in
    let bcases = List.map (fun bcase -> 
        if diff_svl fv_rel (fv bcase) != [] && diff_svl (fv bcase) fv_rel != [] 
        then mkFalse no_pos else bcase) bcases in
    let no_of_disjs = List.length bcases in
    (bcases @ rcases, no_of_disjs)
(*    match bcases with*)
(*    | [bcase] -> ([bcase] @ (List.map (fun rcase -> propagate_rec_helper rcase rel ante_vars) rcases), no_of_disjs)*)
(*    | _ -> (bcases @ (List.map (fun rcase -> propagate_rec_helper rcase rel ante_vars) rcases), no_of_disjs)*)
(*      let new_bcases = remove_weaker_bcase bcases in
        new_bcases @ (List.map (fun rcase -> arr_args rcase rel ante_vars) rcases)*)

let rec no_of_cnts f = match f with
  | BForm _ -> 1
  | And (f1,f2,_) -> (no_of_cnts f1) + (no_of_cnts f2)
  | Or (f1,f2,_,_) -> (no_of_cnts f1) + (no_of_cnts f2)
  | Not (f,_,_) -> no_of_cnts f
  | Forall (_,f,_,_) -> no_of_cnts f
  | Exists (_,f,_,_) -> no_of_cnts f
  | AndList l -> List.fold_left (fun a (_,c)-> a+(no_of_cnts c)) 0 l 

let helper input_pairs rel ante_vars = 
  let pairs = List.filter (fun (p,r) -> CP.equalFormula r rel) input_pairs in
  let pfs,_ = List.split pairs in
  let pfs = List.map (fun p ->
      let noc = no_of_cnts p in
      (*    DD.info_hprint (add_str "NO: " string_of_int) noc no_pos;*)
      let p = if noc > 20 then p else Redlog.elim_exists_with_eq p in
      let p = TP.simplify_raw p in 
      let exists_node_vars = List.filter CP.is_node_typ (CP.fv p) in
      let num_vars, others, num_vars_new = get_num_dom p in
      (*    x_dinfo_hp (add_str "VARS: " (!print_svl)) others no_pos;    *)
      let num_vars = if CP.intersect num_vars others = [] then num_vars else num_vars_new in
      CP.remove_cnts (exists_node_vars@num_vars) p) pfs in
  let pfs,no = propagate_rec pfs rel ante_vars in
  let pfs = List.map (fun p -> 
      let exists_vars = CP.diff_svl (List.filter 
                                       (fun x -> not(CP.is_bag_typ x || CP.is_rel_typ x)) (CP.fv p)) (CP.fv rel) in 
      CP.mkExists exists_vars p None no_pos) pfs in
  match pfs with
  | [] -> []
  (*  | [hd] -> [(rel,hd,no)]*)
  | _ -> [(rel, List.fold_left (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (CP.mkFalse no_pos) pfs, no)]

let simplify_res fixpoint =
  let disjs = list_of_disjs fixpoint in
  match disjs with
  | [p1;p2] -> 
    if TP.imply_raw p1 p2 then p2 else 
    if TP.imply_raw p2 p1 then p1 else fixpoint
  | _ -> fixpoint

let compute_fixpoint_aux rel_fml pf no_of_disjs ante_vars is_recur = 
  if CP.isConstFalse pf then (rel_fml, CP.mkFalse no_pos)
  else (
    let (name,vars) = match rel_fml with
      | CP.BForm ((CP.RelForm (name,args,_),_),_) -> (CP.name_of_spec_var name, (List.concat (List.map CP.afv args)))
      | _ -> report_error no_pos "Wrong format"
    in
    let pre_vars, post_vars = List.partition (fun v -> List.mem v ante_vars) vars in
    try
      let rhs = fixbag_of_pure_formula pf in
      let no = string_of_int no_of_disjs in
      let input_fixbag =  "fixbagA" (*^ name *)^ "(" ^ (string_of_elems pre_vars fixbag_of_spec_var ",") ^ " -> "
                          ^ (string_of_elems post_vars fixbag_of_spec_var ",") ^ ") := " 
                          ^ rhs
      in
      (*print_endline ("\nINPUT: " ^ input_fixbag);*)
      x_dinfo_pp ">>>>>> compute_fixpoint <<<<<<" no_pos;
      x_dinfo_pp ("Input of fixbag: " ^ input_fixbag) no_pos;
      (*      let output_of_sleek = "fixbag.inf" in*)
      (*      let oc = open_out output_of_sleek in*)
      (*      Printf.fprintf oc "%s" input_fixbag;*)
      (*      flush oc;*)
      (*      close_out oc;*)
      let res = syscall (fixbag ^ " \'" ^ input_fixbag ^ "\' \'" ^ no ^ "\'") in
      let res = remove_paren res (String.length res) in
      (*print_endline ("RES: " ^ res);*)
      x_dinfo_pp ("Result of fixbag: " ^ res) no_pos;
      let fixpoint = Parse_fixbag.parse_fix res in 
      x_dinfo_hp (add_str "Result of fixbag (parsed): " (pr_list !CP.print_formula)) fixpoint no_pos;
      match fixpoint with
      | [post] -> (rel_fml, simplify_res post)
      | _ -> report_error no_pos "Expecting a post"
    with _ -> 
      if not(is_rec pf) then 
        let () = x_dinfo_hp (add_str "Input: " !CP.print_formula) pf no_pos in
        let exists_vars = CP.diff_svl (CP.fv_wo_rel pf) (CP.fv rel_fml) in 
        let pf = TP.simplify_exists_raw exists_vars pf in
        (rel_fml, remove_subtract pf)
      else report_error no_pos "Unexpected error in computing fixpoint by FixBag"
  )

let compute_fixpoint input_pairs ante_vars is_rec =
  let (pfs, rels) = List.split input_pairs in
  let rels = Gen.BList.remove_dups_eq CP.equalFormula rels in
  let pairs = match rels with
    | [] -> report_error no_pos "Error in compute_fixpoint"
    (*    | [hd] -> *)
    (*      let pfs,no = propagate_rec pfs hd ante_vars in*)
    (*      let pfs = List.map (fun p -> *)
    (*        let exists_node_vars = List.filter CP.is_node_typ (CP.fv p) in*)
    (*        let p = CP.remove_cnts exists_node_vars p in*)
    (*        let exists_vars = CP.diff_svl (List.filter *)
    (*          (fun x -> not(CP.is_bag_typ x || CP.is_rel_typ x)) (CP.fv p)) (CP.fv hd) in *)
    (*        CP.mkExists exists_vars p None no_pos) pfs in*)
    (*      let pf = List.fold_left (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (CP.mkFalse no_pos) pfs in [(hd,pf,no)]*)
    | _ -> List.concat (List.map (fun r -> helper input_pairs r ante_vars) rels)
  in
  x_tinfo_hp (add_str "input_pairs: " (pr_list (pr_pair !CP.print_formula !CP.print_formula))) input_pairs no_pos;
  List.map (fun (rel_fml,pf,no) -> compute_fixpoint_aux rel_fml pf no ante_vars is_rec) pairs

(*call the wrappers for:
1. trasnform imm formula to imm-free formula and back
2. disable fixcalc inner imm-free to imm transformation (eg. calling simpilfy, etc)  *)
let compute_fixpoint input_pairs ante_vars is_rec =
  let fixpt input_pairs = compute_fixpoint input_pairs ante_vars is_rec in
  let pre  = List.map (fold_pair1f (x_add_1 Immutable.map_imm_to_int_pure_formula)) in
  let post = List.map (fold_pair1f (x_add_1 Immutable.map_int_to_imm_pure_formula)) in
  let fixpt input_pairs = Wrapper.wrap_pre_post_process pre post fixpt input_pairs in
  Wrapper.wrap_one_bool Globals.int2imm_conv false fixpt input_pairs

let compute_fixpoint (i:int) input_pairs pre_vars is_rec =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  Debug.no_2_num i "compute_fixpoint" pr1 pr2 (pr_list (pr_pair pr0 pr0)) 
    (fun _ _ -> compute_fixpoint input_pairs pre_vars is_rec) input_pairs pre_vars
