(*
  Call Fixpoint Calculator, send input to it
*)

open Globals
open Gen.Basic
open Cformula

module Pr = Cprinter
module P = Cpure
module MP = Mcpure

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

let is_self = function
  | P.Var (P.SpecVar (_,id,_),_) -> id=self
  | _ -> false

let is_null = P.is_null

let rec string_of_elems elems string_of sep = match elems with 
  | [] -> ""
  | h::[] -> string_of h 
  | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)

let fixcalc_of_spec_var x = match x with
  | P.SpecVar (_, id, _) -> id

let rec fixcalc_of_exp e = match e with
  | P.Null _ -> "null"
  | P.Var (x, _) -> fixcalc_of_spec_var x
  | P.IConst (i, _) -> string_of_int i
  | P.FConst (f, _) -> string_of_float f
  | P.Add (e1, e2, _) -> fixcalc_of_exp e1 ^ op_add ^ fixcalc_of_exp e2 
  | P.Subtract (e1, e2, _) -> fixcalc_of_exp e1 ^ op_sub ^ "(" ^ fixcalc_of_exp e2 ^ ")"
  | _ -> illegal_format ("Fixcalc.fixcalc_of_exp: Not supported expression")

let rec fixcalc_of_b_formula b =
  let (pf, _) = b in
  match pf with
    | P.BConst (b,_) -> string_of_bool b 
    | P.BVar (x, _) -> fixcalc_of_spec_var x
    | P.Lt (e1, e2, _) -> fixcalc_of_exp e1 ^ op_lt ^ fixcalc_of_exp e2
    | P.Lte (e1, e2, _) -> fixcalc_of_exp e1 ^ op_lte ^ fixcalc_of_exp e2
    | P.Gt (e1, e2, _) -> fixcalc_of_exp e1 ^ op_gt ^ fixcalc_of_exp e2
    | P.Gte (e1, e2, _) -> fixcalc_of_exp e1 ^ op_gte ^ fixcalc_of_exp e2
    | P.Eq (e1, e2, _) -> 
      if (is_self e1 & is_null e2) || (is_self e2 & is_null e1) then self ^ op_lte ^ "0"
      else fixcalc_of_exp e1 ^ op_eq ^ fixcalc_of_exp e2
    | P.Neq (e1, e2, _) ->
      if is_self e1 then 
        let s = fixcalc_of_exp e2 in "((" ^ self ^ op_lt ^ s ^ ")" ^ op_or ^ "(" ^ self ^ op_gt ^ s ^ "))"
      else
      if is_self e2 then 
        let s = fixcalc_of_exp e1 in "((" ^ self ^ op_lt ^ s ^ ")" ^ op_or ^ "(" ^ self ^ op_gt ^ s ^ "))"
      else
        fixcalc_of_exp e1 ^ op_neq ^ fixcalc_of_exp e2
    | _ -> illegal_format ("Fixcalc.fixcalc_of_b_formula: Not supported bformula")

let rec fixcalc_of_pure_formula f = match f with
  | P.BForm (b,_) -> fixcalc_of_b_formula b
  | P.And (p1, p2, _) ->
    "(" ^ fixcalc_of_pure_formula p1 ^ op_and ^ fixcalc_of_pure_formula p2 ^ ")"
  | P.Or (p1, p2,_ , _) -> illegal_format ("Fixcalc.fixcalc_of_pure_formula: Not supported Or-formula")
  | P.Not (p,_ , _) -> illegal_format ("Fixcalc.fixcalc_of_pure_formula: Not supported Not-formula")
  | P.Forall (sv, p,_ , _) ->
    " (forall (" ^ fixcalc_of_spec_var sv ^ ":" ^ fixcalc_of_pure_formula p ^ ")) "
  | P.Exists (sv, p,_ , _) ->
    " (exists (" ^ fixcalc_of_spec_var sv ^ ":" ^ fixcalc_of_pure_formula p ^ ")) "

let rec fixcalc_of_h_formula f = match f with
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2} -> 
    "(" ^ fixcalc_of_h_formula h1 ^ op_and ^ fixcalc_of_h_formula h2 ^ ")"
  | Phase _ -> illegal_format ("Fixcalc.fixcalc_of_h_formula: Not supported Phase-formula")
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2} -> 
    "(" ^ fixcalc_of_h_formula h1 ^ op_or ^ fixcalc_of_h_formula h2 ^ ")"
  | DataNode {h_formula_data_node = sv; h_formula_data_name = c; h_formula_data_arguments = svs} -> 
    if P.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^ (fixcalc_of_spec_var sv) ^ "," ^ (string_of_elems svs fixcalc_of_spec_var ",") ^ ")"
  | ViewNode {h_formula_view_node = sv; h_formula_view_name = c; h_formula_view_arguments = svs} ->
    if P.is_self_spec_var sv then self ^ op_gt ^ "0"
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

let fixcalc = "fixcalc"

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
    let output_of_fixcalc = "fixcalc.out" in
    let ic = open_out output_of_fixcalc in
    Printf.fprintf ic "%s" res;
    close_out ic;
    let _ = syscall ("sed -i /^#/d " ^ output_of_fixcalc) in
    let _ = syscall ("sed -i /^T/d " ^ output_of_fixcalc) in
    let _ = syscall ("sed -i /^$/d " ^ output_of_fixcalc) in
    let res = syscall ("cat " ^ output_of_fixcalc) in
    let new_pf = Parse_fix.parse_fix res in
    let check_imply = Omega.imply new_pf pf "1" 100.0 in
    if check_imply then (
      Pr.fmt_string "INV:  ";
      Pr.pr_angle name (fun x -> Pr.fmt_string (Pr.string_of_typed_spec_var x)) vars;
      Pr.fmt_string ("\nOLD: " ^ (Pr.string_of_pure_formula pf) ^
                     "\nNEW: " ^ (Pr.string_of_pure_formula new_pf) ^ "\n\n");			
      new_pf)
    else pf

  
    
    



