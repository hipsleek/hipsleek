(*
  Call Fixpoint Calculator, send input to it
*)

open Globals
open Gen.Basic
open Cformula

module Pr = Cprinter
module CP = Cpure
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

let is_self = CP.is_self_var

let is_null = CP.is_null

let rec string_of_elems elems string_of sep = match elems with 
  | [] -> ""
  | h::[] -> string_of h 
  | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)

let fixcalc_of_spec_var x = match x with
  | CP.SpecVar (_, id, _) -> id

let rec fixcalc_of_exp e = match e with
  | CP.Null _ -> "null"
  | CP.Var (x, _) -> fixcalc_of_spec_var x
  | CP.IConst (i, _) -> string_of_int i
  | CP.FConst (f, _) -> string_of_float f
  | CP.Add (e1, e2, _) -> fixcalc_of_exp e1 ^ op_add ^ fixcalc_of_exp e2 
  | CP.Subtract (e1, e2, _) -> fixcalc_of_exp e1 ^ op_sub ^ "(" ^ fixcalc_of_exp e2 ^ ")"
  | _ -> illegal_format ("Fixcalc.fixcalc_of_exp: Not supported expression")

let rec fixcalc_of_b_formula b =
  let (pf, _) = b in
  match pf with
    | CP.BConst (b,_) -> string_of_bool b 
    | CP.BVar (x, _) -> fixcalc_of_spec_var x
    | CP.Lt (e1, e2, _) -> fixcalc_of_exp e1 ^ op_lt ^ fixcalc_of_exp e2
    | CP.Lte (e1, e2, _) -> fixcalc_of_exp e1 ^ op_lte ^ fixcalc_of_exp e2
    | CP.Gt (e1, e2, _) -> fixcalc_of_exp e1 ^ op_gt ^ fixcalc_of_exp e2
    | CP.Gte (e1, e2, _) -> fixcalc_of_exp e1 ^ op_gte ^ fixcalc_of_exp e2
    | CP.Eq (e1, e2, _) -> 
      if is_null e2 then fixcalc_of_exp e1 ^ op_lte ^ "0"
      else
      if is_null e1 then fixcalc_of_exp e2 ^ op_lte ^ "0"
      else fixcalc_of_exp e1 ^ op_eq ^ fixcalc_of_exp e2
    | CP.Neq (e1, e2, _) ->
      if is_null e1 then 
        let s = fixcalc_of_exp e2 in s ^ op_gt ^ "0"
      else
      if is_null e2 then 
        let s = fixcalc_of_exp e1 in s ^ op_gt ^ "0"
      else
        let s = fixcalc_of_exp e1 in
        let t = fixcalc_of_exp e2 in
        "((" ^ s ^ op_lt ^ t ^ ")" ^ op_or ^ "(" ^ s ^ op_gt ^ t ^ "))"
    | CP.RelForm (id,args,_) -> (CP.name_of_spec_var id) ^ "(" ^ (string_of_elems args fixcalc_of_exp ",") ^ ")"
    | _ -> illegal_format ("Fixcalc.fixcalc_of_b_formula: Do not support bag, list")

let rec fixcalc_of_pure_formula f = match f with
  | CP.BForm (b,_) -> fixcalc_of_b_formula b
  | CP.And (p1, p2, _) ->
    "(" ^ fixcalc_of_pure_formula p1 ^ op_and ^ fixcalc_of_pure_formula p2 ^ ")"
  | CP.Or (p1, p2,_ , _) ->
    "(" ^ fixcalc_of_pure_formula p1 ^ op_or ^ fixcalc_of_pure_formula p2 ^ ")"
  | CP.Not (p,_ , _) -> illegal_format ("Fixcalc.fixcalc_of_pure_formula: Not supported Not-formula")
  | CP.Forall (sv, p,_ , _) ->
    " (forall (" ^ fixcalc_of_spec_var sv ^ ":" ^ fixcalc_of_pure_formula p ^ ")) "
  | CP.Exists (sv, p,_ , _) ->
    " (exists (" ^ fixcalc_of_spec_var sv ^ ":" ^ fixcalc_of_pure_formula p ^ ")) "

let rec fixcalc_of_h_formula f = match f with
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2} -> 
    "(" ^ fixcalc_of_h_formula h1 ^ op_and ^ fixcalc_of_h_formula h2 ^ ")"
  | Phase _ -> illegal_format ("Fixcalc.fixcalc_of_h_formula: Not supported Phase-formula")
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2} -> 
    "(" ^ fixcalc_of_h_formula h1 ^ op_or ^ fixcalc_of_h_formula h2 ^ ")"
  | DataNode {h_formula_data_node = sv; h_formula_data_name = c; h_formula_data_arguments = svs} -> 
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^ (fixcalc_of_spec_var sv) ^ "," ^ (string_of_elems svs fixcalc_of_spec_var ",") ^ ")"
  | ViewNode {h_formula_view_node = sv; h_formula_view_name = c; h_formula_view_arguments = svs} ->
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^ (fixcalc_of_spec_var sv) ^ "," ^ (string_of_elems svs fixcalc_of_spec_var ",") ^ ")"
  | HTrue -> "True"
  | HFalse -> "False"
  | Hole _ -> illegal_format ("Fixcalc.fixcalc_of_h_formula: Not supported Hole-formula")

let fixcalc_of_mix_formula (f,l) = match f with
  | MCP.MemoF _ -> ""
  | MCP.OnePF pf -> fixcalc_of_pure_formula pf

let rec fixcalc_of_formula e = match e with
  | Or _ -> illegal_format ("Fixcalc.fixcalc_of_formula: Not supported Or-formula")
  | Base {formula_base_heap = h; formula_base_pure = p; formula_base_branches = b} ->
    "(" ^ fixcalc_of_h_formula h ^ op_and ^ fixcalc_of_mix_formula (p,b) ^ ")"
  | Exists {formula_exists_qvars = svs; formula_exists_heap = h; 
    formula_exists_pure = p; formula_exists_branches = b} ->     
    " exists (" ^ (string_of_elems svs fixcalc_of_spec_var ",") ^ ": " ^ 
    fixcalc_of_h_formula h ^ op_and ^ fixcalc_of_mix_formula (p,b) ^ ")"

let fixcalc = "fixcalc_mod"

let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)


let compute_inv name vars fml pf =
  if not !Globals.do_infer_inv then pf
  else
    let output_of_sleek = "fixcalc.inp" in
    let oc = open_out output_of_sleek in
    let input_fixcalc = 
      name ^ ":=" ^ "{" ^ "[" ^ self ^ "," ^ (string_of_elems vars fixcalc_of_spec_var ",") ^ "]" ^ " -> [] -> []: " ^
      (string_of_elems fml (fun (c,_)-> fixcalc_of_formula c) op_or) ^
      "\n};\n\nFix1:=bottomup(" ^ name ^ ",1,SimHeur);\nFix1;\n\n"
    in 
    Printf.fprintf oc "%s" input_fixcalc;
    flush oc;
    close_out oc;
    let res = syscall (fixcalc ^ " " ^ output_of_sleek) in
(*    let output_of_fixcalc = "fixcalc.out" in
    let ic = open_out output_of_fixcalc in
    Printf.fprintf ic "%s" res;
    close_out ic;
    let _ = syscall ("sed -i /^#/d " ^ output_of_fixcalc) in
    let _ = syscall ("sed -i /^T/d " ^ output_of_fixcalc) in
    let _ = syscall ("sed -i /^$/d " ^ output_of_fixcalc) in
    let res = syscall ("cat " ^ output_of_fixcalc) in*)
    let new_pf = List.hd (Parse_fix.parse_fix res) in
    let check_imply = Omega.imply new_pf pf "1" 100.0 in
    if check_imply then (
      Pr.fmt_string "INV:  ";
      Pr.pr_angle name (fun x -> Pr.fmt_string (Pr.string_of_typed_spec_var x)) vars;
      Pr.fmt_string ("\nOLD: " ^ (Pr.string_of_pure_formula pf) ^
                     "\nNEW: " ^ (Pr.string_of_pure_formula new_pf) ^ "\n\n");			
      new_pf)
    else pf

let rec remove_paren s n = if n=0 then "" else match s.[0] with
  | '(' -> remove_paren (String.sub s 1 (n-1)) (n-1)
  | ')' -> remove_paren (String.sub s 1 (n-1)) (n-1)
  | _ -> (String.sub s 0 1) ^ (remove_paren (String.sub s 1 (n-1)) (n-1))

let compute_fixpoint input_pairs =
  let (pfs, rels) = List.split input_pairs in
  let rels = Gen.BList.remove_dups_eq CP.equalFormula rels in
  let rel_fml = match rels with
    | [] -> report_error no_pos "Error in compute_fixpoint"
    | [hd] -> hd
    | _ -> report_error no_pos "Fixcalc.ml: More than one input relation"
  in
  let (name,vars) = match rel_fml with
    | CP.BForm ((CP.RelForm (name,args,_),_),_) -> (CP.name_of_spec_var name, (List.concat (List.map CP.afv args)))
    | _ -> report_error no_pos "Wrong format"
  in
  let pf = List.fold_left (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (List.hd pfs) (List.tl pfs) in  
  try
    let rhs = fixcalc_of_pure_formula pf in 
    let input_fixcalc =  name ^ ":={[" ^ (string_of_elems vars fixcalc_of_spec_var ",") 
      ^ "] -> [] -> []: " ^ rhs ^ "\n};\n\nFix1:=bottomup(" ^ name ^ ",1,SimHeur);\nFix1;\n"
      ^ "Fix2:=topdown(" ^ name ^ ",1,SimHeur);\nFix2;"
    in
    (*print_endline ("\nINPUT: " ^ input_fixcalc);*)
    let output_of_sleek = "fixcalc.inf" in
    let oc = open_out output_of_sleek in
    Printf.fprintf oc "%s" input_fixcalc;
    flush oc;
    close_out oc;
    let res = syscall (fixcalc ^ " " ^ output_of_sleek) in
    let res = remove_paren res (String.length res) in
    (*print_endline ("RES: " ^ res);*)
    let fixpoint = Parse_fix.parse_fix res in
    let fixpoint = List.map (fun f -> 
      let args = CP.fv f in 
      let quan_vars = CP.diff_svl args vars in
      TP.simplify_raw (CP.mkExists quan_vars f None no_pos)) fixpoint in
    match fixpoint with
      | [pre;post] -> (rel_fml, pre, post)
      | _ -> report_error no_pos "Expecting a pair of pre-post"
    (*print_endline ("FIXPOINT: " ^ Cprinter.string_of_pure_formula fixpoint);*)
    (*(rel_fml, List.hd fixpoint)    *)
  with _ -> report_error no_pos "Unexpected error in computing fixpoint"

 


