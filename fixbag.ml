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
  | CP.SpecVar (_, id, _) -> id

let rec fixbag_of_exp e = match e with
(*  | CP.Null _ -> "null"*)
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
    | CP.Lt (e1, e2, _) -> fixbag_of_exp e1 ^ op_lt ^ fixbag_of_exp e2
    | CP.Lte (e1, e2, _) -> fixbag_of_exp e1 ^ op_lte ^ fixbag_of_exp e2
    | CP.Gt (e1, e2, _) -> fixbag_of_exp e1 ^ op_gt ^ fixbag_of_exp e2
    | CP.Gte (e1, e2, _) -> fixbag_of_exp e1 ^ op_gte ^ fixbag_of_exp e2
    | CP.Eq (e1, e2, _) -> fixbag_of_exp e1 ^ op_eq ^ fixbag_of_exp e2
    | CP.Neq (e1, e2, _) -> if List.exists is_int_typ (CP.bfv b) then fixbag_of_exp e1 ^ op_neq ^ fixbag_of_exp e2
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

(*let rec fixbag_of_h_formula f = match f with*)
(*  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2} -> *)
(*    "(" ^ fixbag_of_h_formula h1 ^ op_and ^ fixbag_of_h_formula h2 ^ ")"*)
(*  | Phase _ -> illegal_format ("Fixbag.fixbag_of_h_formula: Not supported Phase-formula")*)
(*  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2} -> *)
(*    "(" ^ fixbag_of_h_formula h1 ^ op_or ^ fixbag_of_h_formula h2 ^ ")"*)
(*  | DataNode {h_formula_data_node = sv; h_formula_data_name = c; h_formula_data_arguments = svs} -> *)
(*    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"*)
(*    else c ^ "(" ^ (fixbag_of_spec_var sv) ^ "," ^ (string_of_elems svs fixbag_of_spec_var ",") ^ ")"*)
(*  | ViewNode {h_formula_view_node = sv; h_formula_view_name = c; h_formula_view_arguments = svs} ->*)
(*    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"*)
(*    else c ^ "(" ^ (fixbag_of_spec_var sv) ^ "," ^ (string_of_elems svs fixbag_of_spec_var ",") ^ ")"*)
(*  | HTrue -> "True"*)
(*  | HFalse -> "False"*)
(*  | Hole _ -> illegal_format ("Fixbag.fixbag_of_h_formula: Not supported Hole-formula")*)

(*let fixbag_of_mix_formula (f,l) = match f with*)
(*  | MCP.MemoF _ -> ""*)
(*  | MCP.OnePF pf -> fixbag_of_pure_formula pf*)

(*let rec fixbag_of_formula e = match e with*)
(*  | Or _ -> illegal_format ("Fixbag.fixbag_of_formula: Not supported Or-formula")*)
(*  | Base {formula_base_heap = h; formula_base_pure = p; formula_base_branches = b} ->*)
(*    "(" ^ fixbag_of_h_formula h ^ op_and ^ fixbag_of_mix_formula (p,b) ^ ")"*)
(*  | Exists {formula_exists_qvars = svs; formula_exists_heap = h; *)
(*    formula_exists_pure = p; formula_exists_branches = b} ->     *)
(*    " exists (" ^ (string_of_elems svs fixbag_of_spec_var ",") ^ ": " ^ *)
(*    fixbag_of_h_formula h ^ op_and ^ fixbag_of_mix_formula (p,b) ^ ")"*)

let fixbag = "fixbag2"

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


(*let compute_inv name vars fml pf =
  if not !Globals.do_infer_inv then pf
  else
    let output_of_sleek = "fixbag.inp" in
    let oc = open_out output_of_sleek in
    let input_fixbag = 
      name ^ ":=" ^ "{" ^ "[" ^ self ^ "," ^ (string_of_elems vars fixbag_of_spec_var ",") ^ "]" ^ " -> [] -> []: " ^
      (string_of_elems fml (fun (c,_)-> fixbag_of_formula c) op_or) ^
      "\n};\n\nFix1:=bottomup(" ^ name ^ ",1,SimHeur);\nFix1;\n\n"
    in 
    Printf.fprintf oc "%s" input_fixbag;
    flush oc;
    close_out oc;
    let res = syscall (fixbag ^ " " ^ output_of_sleek) in
(*    let output_of_fixbag = "fixbag.out" in
    let ic = open_out output_of_fixbag in
    Printf.fprintf ic "%s" res;
    close_out ic;
    let _ = syscall ("sed -i /^#/d " ^ output_of_fixbag) in
    let _ = syscall ("sed -i /^T/d " ^ output_of_fixbag) in
    let _ = syscall ("sed -i /^$/d " ^ output_of_fixbag) in
    let res = syscall ("cat " ^ output_of_fixbag) in*)
    let new_pf = List.hd (Parse_fix.parse_fix res) in
    let check_imply = Omega.imply new_pf pf "1" 100.0 in
    if check_imply then (
      Pr.fmt_string "INV:  ";
      Pr.pr_angle name (fun x -> Pr.fmt_string (Pr.string_of_typed_spec_var x)) vars;
      Pr.fmt_string ("\nOLD: " ^ (Pr.string_of_pure_formula pf) ^
                     "\nNEW: " ^ (Pr.string_of_pure_formula new_pf) ^ "\n\n");			
      new_pf)
    else pf*)

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
    DD.trace_hprint (add_str "input_pairs: " (pr_list (pr_pair !CP.print_formula !CP.print_formula))) input_pairs no_pos;
    DD.devel_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
    DD.devel_pprint ("Input of fixbag: " ^ input_fixbag) no_pos;
    let output_of_sleek = "fixbag.inf" in
    let oc = open_out output_of_sleek in
    Printf.fprintf oc "%s" input_fixbag;
    flush oc;
    close_out oc;
    let res = syscall (fixbag ^ " " ^ output_of_sleek) in
    let res = remove_paren res (String.length res) in
    (*print_endline ("RES: " ^ res);*)
    DD.devel_pprint ("Result of fixbag: " ^ res) no_pos;
    let fixpoint = Parse_fix.parse_fix res in
    DD.devel_hprint (add_str "Result of fixbag (parsed): " (pr_list !CP.print_formula)) fixpoint no_pos;
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
      let id = match id with | CP.SpecVar (t,n,p) -> CP.SpecVar (t,"fixbag" ^ n,p) in
      (CP.BForm ((CP.RelForm (id,new_args,p), o1), o2), [CP.conj_of_list (List.concat subs) no_pos])
    else 
      let args, subs = List.split (List.map (fun a -> substitute a) args) in
      let id = match id with | CP.SpecVar (t,n,p) -> CP.SpecVar (t,"fixbag" ^ n,p) in
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
      | (Subtract (_, Subtract (_,Var (b1,_),_),_), Var (b2,_))
      | (Var (b1,_), Subtract (_, Subtract (_,Var (b2,_),_),_))
      | (Subtract (_, Subtract (_,Var (b1,_),_),_), Subtract (_, Subtract (_,Var (b2,_),_),_))
      -> (eq_spec_var b1 b2 && es != [],[])
      | _ -> (false,[])
    end
  | _ -> (false,[])

let matching f1 f2 = match (f1,f2) with
  | (BForm ((pf1,o),p), BForm ((pf2,_),_)) -> 
(*    DD.devel_hprint (add_str "matching: " (pr_list !CP.print_formula)) [f1;f2] no_pos;*)
    let (res1,res2) = matching_exp pf1 pf2 in
    if res2 = [] then (res1,[])
    else (res1,List.map (fun r2 -> BForm((r2,o),p)) res2)
  | _ -> (false,[])

let can_merge f1 f2 =
  let conjs1 = CP.list_of_conjs f1 in
  let conjs2 = CP.list_of_conjs f2 in
(*    DD.devel_hprint (add_str "CONJ1: " (pr_list !CP.print_formula)) conjs1 no_pos;*)
(*    DD.devel_hprint (add_str "CONJ2: " (pr_list !CP.print_formula)) conjs2 no_pos;*)
  let part_of_f1, others1 = List.partition (fun c -> Gen.BList.mem_eq (CP.equalFormula) c conjs1) conjs2 in
(*DD.devel_hprint (add_str "PART1: " (pr_list !CP.print_formula)) part_of_f1 no_pos;*)
(*DD.devel_hprint (add_str "other1: " (pr_list !CP.print_formula)) others1 no_pos;*)
  let part_of_f2, others2 = List.partition (fun c -> Gen.BList.mem_eq (CP.equalFormula) c conjs2) conjs1 in
(*DD.devel_hprint (add_str "PART2: " (pr_list !CP.print_formula)) part_of_f2 no_pos;*)
(*DD.devel_hprint (add_str "other2: " (pr_list !CP.print_formula)) others2 no_pos;*)
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
(*    DD.devel_hprint (add_str "MERGE: " (pr_list !CP.print_formula)) (snd (List.split can_merge)) no_pos;*)
(*    DD.devel_hprint (add_str "OTHER: " (pr_list !CP.print_formula)) (snd (List.split others)) no_pos;*)
    if can_merge = [] then hd::(simplify tl)
    else
      (* TODO: *)
      let hd = snd (List.hd (List.rev can_merge)) in
      hd::(simplify (snd (List.split others)))

let pre_process vars fmls =
  List.filter (fun f ->
    let vs = List.filter (fun x -> CP.is_bag_typ x || CP.is_bool_typ x) (CP.fv f) in
(*    DD.devel_hprint (add_str "VARS: " !print_svl) vs no_pos;*)
    CP.subset vs vars) fmls

let rec create_alias_tbl vs aset all_rel_vars = match vs with
  | [] -> []
  | [hd] -> [List.filter (fun x -> not(List.mem x all_rel_vars)) (hd::(CP.EMapSV.find_equiv_all hd aset))]
  | hd::tl ->
    let res1 = [List.filter (fun x -> not(List.mem x all_rel_vars)) (hd::(CP.EMapSV.find_equiv_all hd aset))] in
    let tl = List.filter (fun x -> not(List.mem x (List.hd res1))) tl in
    res1@(create_alias_tbl tl aset all_rel_vars)

let propagate_rec_helper rcase_orig rel ante_vars =
  let rel_vars = CP.remove_dups_svl (get_rel_vars rcase_orig) in
(*  DD.devel_hprint (add_str "Before: " (!CP.print_formula)) rcase_orig no_pos;*)
(*  let rcase = TP.simplify_raw (CP.drop_rel_formula rcase_orig) in*)
(*  DD.devel_hprint (add_str "After: " (!CP.print_formula)) rcase no_pos;*)
  let rcase = CP.drop_rel_formula rcase_orig in
  let all_rel_vars = rel_vars @ (CP.fv rel) in
  let als = MCP.ptr_equations_without_null (MCP.mix_of_pure rcase) in
  let aset = CP.EMapSV.build_eset als in
  let other_vars = List.filter (fun x -> CP.is_int_typ x) (CP.fv rcase_orig) in
  let alias = create_alias_tbl (rel_vars@other_vars) aset (CP.fv rel) in
  let subst_lst = List.concat (List.map 
      (fun vars -> 
        if vars = [] then [] 
        else 
          let hd = List.hd vars in 
          List.map (fun v -> (v,hd)) (List.tl vars)
      ) alias) in
(*  DD.devel_hprint (add_str "SUBS: " (pr_list (pr_pair !print_sv !print_sv))) subst_lst no_pos;*)
(*  DD.devel_hprint (add_str "RCASE: " (!CP.print_formula)) rcase no_pos;*)
  let rcase = CP.subst subst_lst rcase in
(*  let rcase = MCP.remove_ptr_equations rcase false in*)
  let rcase = CP.remove_redundant_constraints rcase in
  let rcase = CP.conj_of_list (pre_process all_rel_vars (CP.list_of_conjs rcase)) no_pos in
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

let transform fml v_synch rel = match fml with
  | BForm ((Eq (v1, BagUnion ([b2;Bag([Var (v,_)],_)],_), _), _),_)
  | BForm ((Eq (v1, BagUnion ([Bag([Var (v,_)],_);b2],_), _), _),_)
  | BForm ((Eq (BagUnion ([Bag([Var (v,_)],_);b2],_), v1, _), _),_)
  | BForm ((Eq (BagUnion ([b2;Bag([Var (v,_)],_)],_), v1, _), _),_) -> 
    begin
    match v1 with
    | Var (b1,_)
    | Subtract (_, Subtract (_,Var (b1,_),_),_) ->
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
    | _ -> fml
    end
  | And _ -> 
    let v_synch = List.filter CP.is_int_typ (CP.diff_svl v_synch (CP.fv rel)) in
    let v_subst = List.filter CP.is_int_typ (CP.diff_svl (CP.fv fml) (CP.fv rel)) in
(*    DD.devel_hprint (add_str "VSYNCH: " (!print_svl)) v_synch no_pos;*)
(*    DD.devel_hprint (add_str "VSUBST: " (!print_svl)) v_subst no_pos;*)
    (match (v_subst, v_synch) with
      | ([hd],[v_s]) -> CP.subst [(hd,v_s)] fml
      | _ -> fml
    )
  | _ -> fml

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
(*    DD.devel_hprint (add_str "BCASE: " (pr_list !CP.print_formula)) bcases no_pos;*)
    let bcases = simplify bcases in
(*    DD.devel_hprint (add_str "BCASE: " (pr_list !CP.print_formula)) bcases no_pos;*)
(*    DD.devel_hprint (add_str "RCASE: " (pr_list !CP.print_formula)) rcases no_pos;*)
    let rcases = simplify rcases in
(*    DD.devel_hprint (add_str "RCASE: " (pr_list !CP.print_formula)) rcases no_pos;*)
    let rcases = List.map (fun rcase -> propagate_rec_helper rcase rel ante_vars) rcases in
    let v_synch = List.filter is_int_typ (List.concat (List.map fv rcases)) in
(*    DD.devel_hprint (add_str "BCASE: " (pr_list !CP.print_formula)) bcases no_pos;*)
    let bcases = List.map (fun x -> transform x v_synch rel) bcases in
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

let helper input_pairs rel ante_vars = 
  let pairs = List.filter (fun (p,r) -> CP.equalFormula r rel) input_pairs in
  let pfs,_ = List.split pairs in
  let pfs = List.map (fun p ->
    let noc = no_of_cnts p in
(*    DD.info_hprint (add_str "NO: " string_of_int) noc no_pos;*)
    let p = if noc > 20 then p else Redlog.elim_exists_with_eq p in
    let p = TP.simplify_raw p in 
    let exists_node_vars = List.filter CP.is_node_typ (CP.fv p) in
    let num_vars = get_num_dom p in
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

let compute_fixpoint_aux rel_fml pf no_of_disjs ante_vars = 
  if CP.isConstFalse pf then (rel_fml, CP.mkFalse no_pos, CP.mkFalse no_pos)
  else (
    let (name,vars) = match rel_fml with
      | CP.BForm ((CP.RelForm (name,args,_),_),_) -> (CP.name_of_spec_var name, (List.concat (List.map CP.afv args)))
      | _ -> report_error no_pos "Wrong format"
    in
    let pre_vars, post_vars = List.partition (fun v -> List.mem v ante_vars) vars in
    try
      let rhs = fixbag_of_pure_formula pf in
      let no = string_of_int no_of_disjs in
      let input_fixbag =  "fixbag" ^ name ^ "(" ^ (string_of_elems pre_vars fixbag_of_spec_var ",") ^ " -> "
        ^ (string_of_elems post_vars fixbag_of_spec_var ",") ^ ") := " 
        ^ rhs
      in
      (*print_endline ("\nINPUT: " ^ input_fixbag);*)
      DD.devel_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
      DD.devel_pprint ("Input of fixbag: " ^ input_fixbag) no_pos;
(*      let output_of_sleek = "fixbag.inf" in*)
(*      let oc = open_out output_of_sleek in*)
(*      Printf.fprintf oc "%s" input_fixbag;*)
(*      flush oc;*)
(*      close_out oc;*)
      let res = syscall (fixbag ^ " \'" ^ input_fixbag ^ "\' \'" ^ no ^ "\'") in
      let res = remove_paren res (String.length res) in
      (*print_endline ("RES: " ^ res);*)
      DD.devel_pprint ("Result of fixbag: " ^ res) no_pos;
      let fixpoint = Parse_fixbag.parse_fix res in
      DD.devel_hprint (add_str "Result of fixbag (parsed): " (pr_list !CP.print_formula)) fixpoint no_pos;
      match fixpoint with
        | [post] -> (rel_fml, post, CP.mkTrue no_pos)
        | _ -> report_error no_pos "Expecting a post"
    with _ -> report_error no_pos "Unexpected error in computing fixpoint")

let compute_fixpoint input_pairs ante_vars =
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
  DD.trace_hprint (add_str "input_pairs: " (pr_list (pr_pair !CP.print_formula !CP.print_formula))) input_pairs no_pos;
  List.map (fun (rel_fml,pf,no) -> compute_fixpoint_aux rel_fml pf no ante_vars) pairs

let compute_fixpoint (i:int) input_pairs pre_vars =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  Debug.no_2_num i "compute_fixpoint" pr1 pr2 (pr_list (pr_triple pr0 pr0 pr0)) 
      (fun _ _ -> compute_fixpoint input_pairs pre_vars) input_pairs pre_vars

 


