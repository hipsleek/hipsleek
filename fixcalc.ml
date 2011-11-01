(*
  Call Fixpoint Calculator, send input to it
*)

open Globals
open Gen.Basic
open Cformula

module Pr = Cprinter
module P = Cpure
module MP = Mcpure

let fixcalc = "fixcalc";;
let output = "fixcalc.inp";;
let oc = ref (open_out output);;

let fmt_string x = Printf.fprintf (!oc) "%s" x
let fmt_bool x = Printf.fprintf (!oc) "%b" x
let fmt_int x = Printf.fprintf (!oc) "%d" x
let fmt_float x = Printf.fprintf (!oc) "%f" x

let op_lt = "<" 
let op_lte = "<=" 
let op_gt = ">" 
let op_gte = ">=" 
let op_eq = "=" 
let op_neq = "!=" 

let list_iter op f xs = 
	f (List.hd xs); List.iter (fun x -> fmt_string op; f x;) (List.tl xs);;
let pr_square f xs = 
	fmt_string "[self"; List.iter (fun x -> fmt_string ","; f x;) xs; fmt_string "]";;
let pr_bracket f xs s = 
	fmt_string ("(" ^ s); List.iter (fun x -> fmt_string ","; f x;) xs; fmt_string ")";;


let string_of_spec_var x = match x with
  | P.SpecVar (t, id, p) -> id

let fixcalc_of_spec_var x = fmt_string (string_of_spec_var x) 

let rec fixcalc_of_exp e = match e with
  | P.Null l -> fmt_string "null"
  | P.Var (x, l) -> fixcalc_of_spec_var x
  | P.IConst (i, l) -> fmt_int i
  | P.FConst (f, l) -> fmt_float f
  | P.Add (e1, e2, l) -> fixcalc_of_exp e1; fmt_string "+"; fixcalc_of_exp e2 
  | _ -> failwith ("Fixcalc.fixcalc_of_exp: Not supported expression")

let rec fixcalc_of_b_formula b =
  let (pf, _) = b in
  match pf with
    | P.BConst (b,l) -> fmt_bool b 
    | P.BVar (x, l) -> fixcalc_of_spec_var x
    | P.Lt (e1, e2, l) -> fixcalc_of_exp e1; fmt_string op_lt ; fixcalc_of_exp e2
    | P.Lte (e1, e2, l) -> fixcalc_of_exp e1; fmt_string op_lte ; fixcalc_of_exp e2
    | P.Gt (e1, e2, l) -> fixcalc_of_exp e1; fmt_string op_gt ; fixcalc_of_exp e2
    | P.Gte (e1, e2, l) -> fixcalc_of_exp e1; fmt_string op_gte ; fixcalc_of_exp e2
    | P.Eq (P.Var(P.SpecVar (_,"self",_),_), P.Null _, l) -> fmt_string "self <= 0";
    | P.Eq (P.Null _, P.Var(P.SpecVar (_,"self",_),_), l) -> fmt_string "self <= 0";
    | P.Eq (e1, e2, l) -> fixcalc_of_exp e1; fmt_string op_eq ; fixcalc_of_exp e2
    | P.Neq (P.Var(P.SpecVar (_,"self",_),_), e2, l) -> 
      fmt_string "("; fmt_string "("; fmt_string "self < "; fixcalc_of_exp e2; 
      fmt_string ") || (self > "; fixcalc_of_exp e2; fmt_string ")"; fmt_string ")";
    | P.Neq (e2, P.Var(P.SpecVar (_,"self",_),_), l) -> 
      fmt_string "("; fmt_string "("; fmt_string "self < "; fixcalc_of_exp e2; 
      fmt_string ") || (self > "; fixcalc_of_exp e2; fmt_string ")"; fmt_string ")";
    | P.Neq (e1, e2, l) -> fixcalc_of_exp e1; fmt_string op_neq ; fixcalc_of_exp e2
    | _ -> failwith ("Fixcalc.fixcalc_of_b_formula: Not supported bformula")

let rec fixcalc_of_pure_formula f = match f with
  | P.BForm (b,_) ->
		fixcalc_of_b_formula b;
  | P.And (p1, p2, _) ->
		fmt_string "("; fixcalc_of_pure_formula p1; fmt_string " && "; 
		fixcalc_of_pure_formula p2; fmt_string ")"
  | P.Or (p1, p2,_ , _) ->
		failwith ("Fixcalc.fixcalc_of_pure_formula: Not supported Or-formula")
  | P.Not (p,_ , _) ->
		failwith ("Fixcalc.fixcalc_of_pure_formula: Not supported Not-formula")
  | P.Forall (sv, p,_ , _) ->
		fmt_string " (forall ("; fixcalc_of_spec_var sv; fmt_string ":"; 
		fixcalc_of_pure_formula p; fmt_string ")) "
  | P.Exists (sv, p,_ , _) ->
		fmt_string " (exists ("; fixcalc_of_spec_var sv; fmt_string ":"; 
		fixcalc_of_pure_formula p; fmt_string ")) "

let rec fixcalc_of_cformula f = match f with
  | Star ({h_formula_star_h1 = h1; h_formula_star_h2 = h2; h_formula_star_pos = pos}) -> 
    fmt_string "("; fixcalc_of_cformula h1; fmt_string " && "; 
		fixcalc_of_cformula h2; fmt_string ")"
  | Phase ({h_formula_phase_rd = h1; h_formula_phase_rw = h2; h_formula_phase_pos = pos}) -> 
		failwith ("Fixcalc.fixcalc_of_cformula: Not supported Phase-formula")
  | Conj ({h_formula_conj_h1 = h1; h_formula_conj_h2 = h2; h_formula_conj_pos = pos}) -> 
    fmt_string "("; fixcalc_of_cformula h1; fmt_string " || "; 
		fixcalc_of_cformula h2; fmt_string ")"
  | DataNode ({h_formula_data_node = sv; h_formula_data_name = c;
    h_formula_data_imm = imm; h_formula_data_arguments = svs;
    h_formula_data_holes = hs; h_formula_data_pos = pos;
    h_formula_data_remaining_branches = ann; h_formula_data_label = pid})-> 
    let _ = match sv with
      | P.SpecVar (t, "self", p) -> fmt_string "self > 0"
      | _ -> 
				fmt_string c; pr_bracket (fun x -> fixcalc_of_spec_var x) svs (string_of_spec_var sv);
		in ()
  | ViewNode ({h_formula_view_node = sv; h_formula_view_name = c; 
    h_formula_view_imm = imm; h_formula_view_arguments = svs; 
    h_formula_view_origins = origs; h_formula_view_original = original;
    h_formula_view_lhs_case = lhs_case; h_formula_view_label = pid;
    h_formula_view_remaining_branches = ann; h_formula_view_pruning_conditions = pcond;
    h_formula_view_pos =pos}) ->
    let _ = match sv with
      | P.SpecVar (t, "self", p) -> fmt_string "self > 0";
      | _ -> 
				fmt_string c; pr_bracket (fun x -> fixcalc_of_spec_var x) svs (string_of_spec_var sv);
    in ()
  | HTrue -> fmt_string "True"
  | HFalse -> fmt_string "False"
  | Hole m -> failwith ("Fixcalc.fixcalc_of_cformula: Not supported Hole-formula")

let  pr_memo_pure_formula_branches (f, l) = ()
let  pr_pure_formula_branches (f, l) = fixcalc_of_pure_formula f

let pr_mix_formula_branches (f,l) = match f with
  | MCP.MemoF f -> pr_memo_pure_formula_branches (f,l)
  | MCP.OnePF f -> pr_pure_formula_branches (f,l)

let rec fixcalc_of_formula e = match e with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) -> 
		failwith ("Fixcalc.fixcalc_of_formula: Not supported Or-formula")
  | Base ({formula_base_heap = h; formula_base_pure = p; 
	  formula_base_branches = b; formula_base_type = t;
    formula_base_flow = fl; formula_base_label = lbl; formula_base_pos = pos}) ->
    fmt_string "("; fixcalc_of_cformula h ; fmt_string " && " ; 
		pr_mix_formula_branches(p,b); fmt_string ")"
  | Exists ({formula_exists_qvars = svs; formula_exists_heap = h; 
	  formula_exists_pure = p; formula_exists_branches = b;
    formula_exists_type = t; formula_exists_flow = fl; 
		formula_exists_label = lbl; formula_exists_pos = pos}) ->
    fmt_string " exists ("; list_iter "," (fun x -> fixcalc_of_spec_var x) svs;
		fmt_string ": "; fixcalc_of_cformula h; fmt_string " && " ; 
		pr_mix_formula_branches(p,b); fmt_string ")"

let compute_inv name vars fml pf =
  let syscall cmd =
  let ic, oc3 = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  let _ = Unix.close_process (ic, oc3) in (Buffer.contents buf) 
	in 
	if !Globals.do_infer_inv then
  begin
		fmt_string (name ^ ":=" ^ "{");
    pr_square (fun x -> fixcalc_of_spec_var x) vars; 
    fmt_string " -> [] -> []: ";
    list_iter " || " (fun (c,_)-> fixcalc_of_formula c) fml;
    Printf.fprintf (!oc) "\n};\n\nFix1:=bottomup(%s,1,SimHeur);\nFix1;\n\n" name;
    flush (!oc);
    close_out (!oc);
    let output2 = "fixcalc.out" in
    let oc2 = open_out output2 in
    let res = syscall (fixcalc ^ " " ^ output) in
    oc := open_out output;
    Printf.fprintf oc2 "%s" res;
    close_out oc2;
    let _ = syscall ("sed -i /^#/d " ^ output2) in
    let _ = syscall ("sed -i /^T/d " ^ output2) in
    let _ = syscall ("sed -i /^$/d " ^ output2) in
    let string = syscall ("cat " ^ output2) in
    let new_pf = Parse_fix.parse_fix string in
(*  print_string res;*)
(*  print_endline (Cprinter.string_of_pure_formula new_pf ^ "a");*)
    let check_impl = Omega.imply new_pf pf "1" 100 in
    if check_impl then
    begin
      Pr.fmt_string "INV:  ";
      Pr.pr_angle name (fun x -> Pr.fmt_string (Pr.string_of_typed_spec_var x)) vars;
      Pr.fmt_string ("\nOLD: " ^ (Pr.string_of_pure_formula pf) ^
                     "\nNEW: " ^ (Pr.string_of_pure_formula new_pf) ^ "\n\n");			
      new_pf
    end
    else pf
  end
  else pf

  
    
    



