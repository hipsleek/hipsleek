(*
  Call Fixpoint Calculator, send input to it
*)

open Globals
module DD = Debug
open Gen
open Exc.GTable
open Perm
open Cformula
open Context
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
  | CP.SpecVar (Named _, id, Unprimed) -> "NOD" ^ id
  | CP.SpecVar (Named _, id, Primed) -> "NODPRI" ^ id
  | CP.SpecVar (_, id, Unprimed) -> id
  | CP.SpecVar (_, id, Primed) -> "PRI" ^ id

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
    | CP.RelForm (id,args,_) -> (fixcalc_of_spec_var id) ^ "(" ^ (string_of_elems args fixcalc_of_exp ",") ^ ")"
    | _ -> illegal_format ("Fixcalc.fixcalc_of_b_formula: Do not support bag, list")

let rec fixcalc_of_pure_formula f = match f with
  | CP.BForm ((CP.BVar (x,_),_),_) -> fixcalc_of_spec_var x ^ op_gt ^ "0"
  | CP.BForm (b,_) -> fixcalc_of_b_formula b
  | CP.And (p1, p2, _) ->
    "(" ^ fixcalc_of_pure_formula p1 ^ op_and ^ fixcalc_of_pure_formula p2 ^ ")"
  | CP.Or (p1, p2,_ , _) ->
    "(" ^ fixcalc_of_pure_formula p1 ^ op_or ^ fixcalc_of_pure_formula p2 ^ ")"
  | CP.Not (p,_ , _) -> 
    begin
    match p with
    | CP.BForm ((CP.BVar (x,_),_),_) -> fixcalc_of_spec_var x ^ op_lte ^ "0"
    | _ -> illegal_format ("Fixcalc.fixcalc_of_pure_formula: Not supported Not-formula")
    end
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

(*let compute_fixpoint input_pairs =
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
    DD.trace_hprint (add_str "input_pairs: " (pr_list (pr_pair !CP.print_formula !CP.print_formula))) input_pairs no_pos;
    DD.devel_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
    DD.devel_pprint ("Input of fixcalc: " ^ input_fixcalc) no_pos;
    let output_of_sleek = "fixcalc.inf" in
    let oc = open_out output_of_sleek in
    Printf.fprintf oc "%s" input_fixcalc;
    flush oc;
    close_out oc;
    let res = syscall (fixcalc ^ " " ^ output_of_sleek) in
    let res = remove_paren res (String.length res) in
    (*print_endline ("RES: " ^ res);*)
    DD.devel_pprint ("Result of fixcalc: " ^ res) no_pos;
    let fixpoint = Parse_fix.parse_fix res in
    DD.devel_hprint (add_str "Result of fixcalc (parsed): " (pr_list !CP.print_formula)) fixpoint no_pos;
    let fixpoint = List.map (fun f -> 
        let args = CP.fv f in 
        let quan_vars = CP.diff_svl args vars in
        TP.simplify_raw (CP.mkExists quan_vars f None no_pos)) fixpoint in
    match fixpoint with
      | [pre;post] -> (rel_fml, pre, post)
      | _ -> report_error no_pos "Expecting a pair of pre-post"
  with _ -> report_error no_pos "Unexpected error in computing fixpoint"*)

let arr_para_order (rel: CP.formula) (rel_def: CP.formula) (ante_vars: CP.spec_var list) : CP.formula = match (rel,rel_def) with
  | (CP.BForm ((CP.RelForm (id,args,p), o1), o2), CP.BForm ((CP.RelForm (id_def,args_def,_), _), _)) -> 
    if id = id_def then 
      let new_args_def = 
        let pre_args, post_args = List.partition (fun e -> Gen.BList.subset_eq CP.eq_spec_var (CP.afv e) ante_vars) args_def in
        pre_args @ post_args 
      in
      let pairs = List.combine args_def args in
      let new_args = List.map (fun a -> List.assoc a pairs) new_args_def in
      CP.BForm ((CP.RelForm (id,new_args,p), o1), o2)
    else rel
  | _ -> report_error no_pos "Expecting relation formulae"

let rec is_rec pf = match pf with
  | CP.BForm (bf,_) -> CP.is_RelForm pf
  | CP.And (f1,f2,_) -> is_rec f1 || is_rec f2
  | CP.Or (f1,f2,_,_) -> is_rec f1 || is_rec f2
  | CP.Not (f,_,_) -> is_rec f
  | CP.Forall (_,f,_,_) -> is_rec f
  | CP.Exists (_,f,_,_) -> is_rec f

let rec get_rel_vars pf = match pf with
  | CP.BForm (bf,_) -> if CP.is_RelForm pf then CP.fv pf else []
  | CP.And (f1,f2,_) -> get_rel_vars f1 @ get_rel_vars f2
  | CP.Or (f1,f2,_,_) -> get_rel_vars f1 @ get_rel_vars f2
  | CP.Not (f,_,_) -> get_rel_vars f
  | CP.Forall (_,f,_,_) -> get_rel_vars f
  | CP.Exists (_,f,_,_) -> get_rel_vars f

let propagate_exp exp1 exp2 = match (exp1, exp2) with (* Need to cover all patterns *)
  | (CP.Lte(e1, CP.IConst(i2, _), _), CP.Lte(e3, CP.IConst(i4, _), _)) ->
    if CP.eqExp e1 e3 && i2 > i4 then Some (CP.Lte(e1, CP.IConst(i4, no_pos), no_pos)) else None
  | (CP.Lte(e1, CP.IConst(i2, _), _), CP.Eq(e3, CP.IConst(i4, _), _))
  | (CP.Lte(e1, CP.IConst(i2, _), _), CP.Eq(CP.IConst(i4, _), e3, _)) ->
    if CP.eqExp e1 e3 && i2 > i4 then Some (CP.Lte(e1, CP.IConst(i4, no_pos), no_pos)) else None
  | (CP.Lte(CP.IConst(i2, _), e1, _), CP.Eq(e3, CP.IConst(i4, _), _))
  | (CP.Lte(CP.IConst(i2, _), e1, _), CP.Eq(CP.IConst(i4, _), e3, _)) ->
    if CP.eqExp e1 e3 && i2 < i4 then Some (CP.Gte(e1, CP.IConst(i4, no_pos), no_pos)) else None
  | (CP.Lte(e1, CP.IConst(i2, _), _), CP.Lt(e3, CP.IConst(i4, _), _)) ->
    if CP.eqExp e1 e3 && i2 >= i4 then Some (CP.Lt(e1, CP.IConst(i4, no_pos), no_pos)) else None
  | (CP.Gte(e1, CP.IConst(i2, _), _), CP.Gte(e3, CP.IConst(i4, _), _)) ->
    if CP.eqExp e1 e3 && i2 < i4 then Some (CP.Gte(e1, CP.IConst(i4, no_pos), no_pos)) else None
  | (CP.Gte(e1, CP.IConst(i2, _), _), CP.Eq(e3, CP.IConst(i4, _), _))
  | (CP.Gte(e1, CP.IConst(i2, _), _), CP.Eq(CP.IConst(i4, _), e3, _)) ->
    if CP.eqExp e1 e3 && i2 < i4 then Some (CP.Gte(e1, CP.IConst(i4, no_pos), no_pos)) else None
  | (CP.Gte(e1, CP.IConst(i2, _), _), CP.Gt(e3, CP.IConst(i4, _), _)) ->
    if CP.eqExp e1 e3 && i2 <= i4 then Some (CP.Gt(e1, CP.IConst(i4, no_pos), no_pos)) else None
  | _ -> None  

let propagate_exp exp1 exp2 = 
  let pr0 = !CP.print_p_formula in
  Debug.no_2 "propagate_exp" pr0 pr0 (pr_option pr0)
      (fun _ _ -> propagate_exp exp1 exp2) exp1 exp2

let propagate_fml rcase bcase = match (rcase, bcase) with
  | (CP.BForm ((exp1,_),_), CP.BForm ((exp2,_),_)) -> 
    let exp = propagate_exp exp1 exp2 in
    (match exp with
    | None -> []
    | Some e -> [CP.BForm ((e,None),None)])
  | _ -> []

let propagate_fml rcase bcase = 
  let pr0 = !CP.print_formula in
  Debug.no_2 "propagate_fml" pr0 pr0 (pr_list pr0)
      (fun _ _ -> propagate_fml rcase bcase) rcase bcase

let propagate_rec_helper rcase_orig bcase_orig rel ante_vars =
  let rel_vars = CP.remove_dups_svl (get_rel_vars rcase_orig) in
  let rcase = TP.simplify_raw (CP.drop_rel_formula rcase_orig) in
  let rels = CP.get_RelForm rcase_orig in
  let rels = List.map (fun r -> arr_para_order r rel ante_vars) rels in
  let exists_vars = CP.diff_svl (CP.fv rcase) rel_vars in
  let rcase2 = TP.simplify_raw (CP.mkExists exists_vars rcase None no_pos) in
  try
    let pairs = List.combine (CP.fv rel) rel_vars in
    let bcase = CP.subst pairs bcase_orig in
    let pf = List.concat (List.map (fun b -> List.concat 
        (List.map (fun r -> propagate_fml r b) (CP.list_of_conjs rcase2))) (CP.list_of_conjs bcase)) in
    CP.conj_of_list ([rcase]@rels@pf) no_pos
  (*  print_endline ("PURE: " ^ Cprinter.string_of_pure_formula rcase);*)
  (*  print_endline ("PURE2: " ^ Cprinter.string_of_pure_formula bcase);*)
  (*  print_endline ("PURE3: " ^ Cprinter.string_of_pure_formula pf);*)
  with _ -> rcase_orig

let propagate_rec pfs rel ante_vars = match CP.get_rel_id rel with
  | None -> pfs
  | Some ivs ->
    let (rcases, bcases) = List.partition is_rec pfs in
    match bcases with
    | [bcase] -> [bcase] @ (List.map (fun rcase -> propagate_rec_helper rcase bcase rel ante_vars) rcases)
    | _ -> pfs

let helper input_pairs rel ante_vars = 
  let pairs = List.filter (fun (p,r) -> CP.equalFormula r rel) input_pairs in
  let pfs,_ = List.split pairs in
  let pfs = propagate_rec pfs rel ante_vars in
  let pfs = List.map (fun p -> let exists_vars = CP.diff_svl (CP.fv p) (CP.fv rel) in 
      CP.mkExists exists_vars p None no_pos) pfs in
  match pfs with
  | [] -> []
  | [hd] -> [(rel,hd)]
  | _ -> [(rel, List.fold_left (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (List.hd pfs) (List.tl pfs))]

let compute_fixpoint_aux rel_fml pf ante_vars = 
  let (name,vars) = match rel_fml with
    | CP.BForm ((CP.RelForm (name,args,_),_),_) -> (CP.name_of_spec_var name, (List.concat (List.map CP.afv args)))
    | _ -> report_error no_pos "Wrong format"
  in
  let pre_vars, post_vars = List.partition (fun v -> List.mem v ante_vars) vars in
  try
    let rhs = fixcalc_of_pure_formula pf in 
    let input_fixcalc =  name ^ ":={[" ^ (string_of_elems pre_vars fixcalc_of_spec_var ",") ^ "] -> "
      ^ "[" ^ (string_of_elems post_vars fixcalc_of_spec_var ",") ^ "] -> []: " 
      ^ rhs ^ "\n};\n\nFix1:=bottomup(" ^ name ^ ",1,SimHeur);\nFix1;\n"
      ^ "Fix2:=topdown(" ^ name ^ ",1,SimHeur);\nFix2;"
    in
    (*print_endline ("\nINPUT: " ^ input_fixcalc);*)
    DD.devel_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
    DD.devel_pprint ("Input of fixcalc: " ^ input_fixcalc) no_pos;
    let output_of_sleek = "fixcalc.inf" in
    let oc = open_out output_of_sleek in
    Printf.fprintf oc "%s" input_fixcalc;
    flush oc;
    close_out oc;
    let res = syscall (fixcalc ^ " " ^ output_of_sleek) in
    let res = remove_paren res (String.length res) in
    (*print_endline ("RES: " ^ res);*)
    DD.devel_pprint ("Result of fixcalc: " ^ res) no_pos;
    let fixpoint = Parse_fix.parse_fix res in
    DD.devel_hprint (add_str "Result of fixcalc (parsed): " (pr_list !CP.print_formula)) fixpoint no_pos;
    (*let fixpoint = List.map (fun f -> 
        let args = CP.fv f in 
        let quan_vars = CP.diff_svl args vars in
        let new_f = CP.wrap_exists_svl f quan_vars in
        let new_f = Redlog.elim_exists_with_eq new_f in
        let new_f = CP.arith_simplify_new new_f in new_f) fixpoint in*)
    match fixpoint with
      | [pre;post] -> (rel_fml, pre, post)
      | _ -> report_error no_pos "Expecting a pair of pre-post"
  with _ -> report_error no_pos "Unexpected error in computing fixpoint"

let compute_fixpoint input_pairs ante_vars =
  let (pfs, rels) = List.split input_pairs in
  let rels = Gen.BList.remove_dups_eq CP.equalFormula rels in
  let pairs = match rels with
    | [] -> report_error no_pos "Error in compute_fixpoint"
    | [hd] -> 
      let pfs = propagate_rec pfs hd ante_vars in
      let pfs = List.map (fun p -> let exists_vars = CP.diff_svl (CP.fv p) (CP.fv hd) in 
          CP.mkExists exists_vars p None no_pos) pfs in
      let pf = List.fold_left (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (List.hd pfs) (List.tl pfs) in [(hd,pf)]
    | _ -> List.concat (List.map (fun r -> helper input_pairs r ante_vars) rels)
  in
  DD.trace_hprint (add_str "input_pairs: " (pr_list (pr_pair !CP.print_formula !CP.print_formula))) input_pairs no_pos;
  List.map (fun (rel_fml,pf) -> compute_fixpoint_aux rel_fml pf ante_vars) pairs


(*
type: (CP.formula * CP.formula) list ->
  (CP.formula * TP.CP.formula * TP.CP.formula) list

type: (CP.formula * CP.formula) list ->
  CP.formula * TP.CP.formula * TP.CP.formula
*)
let compute_fixpoint (i:int) input_pairs pre_vars =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  Debug.no_2_num i "compute_fixpoint" pr1 pr2 (pr_list (pr_triple pr0 pr0 pr0)) 
      (fun _ _ -> compute_fixpoint input_pairs pre_vars) input_pairs pre_vars

 


