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

let rec fixcalc_of_exp_list e op number = match number with
  | 0 -> ""
  | 1 -> fixcalc_of_exp e
  | n -> fixcalc_of_exp e ^ op ^ (fixcalc_of_exp_list e op (n-1))

and fixcalc_of_exp e = match e with
  | CP.Null _ -> "null"
  | CP.Var (x, _) -> fixcalc_of_spec_var x
  | CP.IConst (i, _) -> string_of_int i
  | CP.FConst (f, _) -> string_of_float f
  | CP.Add (e1, e2, _) -> fixcalc_of_exp e1 ^ op_add ^ fixcalc_of_exp e2 
  | CP.Subtract (e1, e2, _) -> fixcalc_of_exp e1 ^ op_sub ^ "(" ^ fixcalc_of_exp e2 ^ ")"
  | CP.Mult (e1, e2, _) -> 
    begin
      match e1, e2 with
      | (CP.IConst (i,_),_) -> fixcalc_of_exp_list e2 op_add i
      | (_,CP.IConst (i,_)) -> fixcalc_of_exp_list e1 op_add i
      | _ -> illegal_format ("Fixcalc.fixcalc_of_exp: Not supported expression")
    end
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
    | CP.RelForm (id,args,_) -> 
      if List.exists (fun x -> match x with | CP.IConst _ -> true | _ -> false) args then "0=0"
      else
        (fixcalc_of_spec_var id) ^ "(" ^ (string_of_elems args fixcalc_of_exp ",") ^ ")"
    | _ -> illegal_format ("Fixcalc.fixcalc_of_b_formula: Do not support bag, list")

let rec fixcalc_of_pure_formula f = match f with
  | CP.BForm ((CP.BVar (x,_),_),_) -> fixcalc_of_spec_var x ^ op_gt ^ "0"
  | CP.BForm (b,_) -> fixcalc_of_b_formula b
  | CP.And (p1, p2, _) ->
    "(" ^ fixcalc_of_pure_formula p1 ^ op_and ^ fixcalc_of_pure_formula p2 ^ ")"
  | CP.AndList b -> (match b with | [] -> fixcalc_of_pure_formula (CP.mkFalse no_pos) | (_,x)::t -> 
	fixcalc_of_pure_formula (List.fold_left (fun a (_,c)->CP.mkAnd a c no_pos) x t))
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
  | HTrue -> "HTrue"
  | HFalse -> "HFalse"
  | HEmp -> "Emp"
  | Hole _ -> illegal_format ("Fixcalc.fixcalc_of_h_formula: Not supported Hole-formula")

let fixcalc_of_mix_formula f = match f with
  | MCP.MemoF _ -> ""
  | MCP.OnePF pf -> fixcalc_of_pure_formula pf

let rec fixcalc_of_formula e = match e with
  | Or _ -> illegal_format ("Fixcalc.fixcalc_of_formula: Not supported Or-formula")
  | Base {formula_base_heap = h; formula_base_pure = p} ->
    "(" ^ fixcalc_of_h_formula h ^ op_and ^ fixcalc_of_mix_formula p ^ ")"
  | Exists {formula_exists_qvars = svs; formula_exists_heap = h; formula_exists_pure = p} ->     
    " exists (" ^ (string_of_elems svs fixcalc_of_spec_var ",") ^ ": " ^ 
    fixcalc_of_h_formula h ^ op_and ^ fixcalc_of_mix_formula p ^ ")"

let fixcalc = "fixcalc"
let fixcalc_old = "fixcalc_mod"

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
      "\n};\n\nFix1:=bottomupgen([" ^ name ^ "]);\n\n"
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


let rec is_rec pf = match pf with
  | CP.BForm (bf,_) -> CP.is_RelForm pf
  | CP.And (f1,f2,_) -> is_rec f1 || is_rec f2
  | CP.AndList b -> exists_l_snd is_rec b
  | CP.Or (f1,f2,_,_) -> is_rec f1 || is_rec f2
  | CP.Not (f,_,_) -> is_rec f
  | CP.Forall (_,f,_,_) -> is_rec f
  | CP.Exists (_,f,_,_) -> is_rec f

let rec get_rel_vars pf = match pf with
  | CP.BForm (bf,_) -> if CP.is_RelForm pf then CP.fv pf else []
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
      let var = CP.fresh_spec_var_prefix "fc" arb in
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
      (CP.BForm ((CP.RelForm (id,new_args,p), o1), o2), [CP.conj_of_list (List.concat subs) no_pos])
    else 
      let args, subs = List.split (List.map (fun a -> substitute a) args) in
      (CP.BForm ((CP.RelForm (id,args,p), o1), o2), [CP.conj_of_list (List.concat subs) no_pos])
  | _ -> report_error no_pos "Expecting relation formulae"

let arr_args rcase_orig rel ante_vars = 
  let rels = CP.get_RelForm rcase_orig in
  let rels,lp = List.split (List.map (fun r -> arr_para_order r rel ante_vars) rels) in
  let rcase = TP.simplify_raw (CP.drop_rel_formula rcase_orig) in
  CP.conj_of_list ([rcase]@rels@(List.concat lp)) no_pos

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
  let rels,lp = List.split (List.map (fun r -> arr_para_order r rel ante_vars) rels) in
  let exists_vars = CP.diff_svl (CP.fv rcase) rel_vars in
  let rcase2 = TP.simplify_raw (CP.mkExists exists_vars rcase None no_pos) in
  try
    let pairs = List.combine (CP.fv rel) rel_vars in
    let bcase = CP.subst pairs bcase_orig in
    let pf = List.concat (List.map (fun b -> List.concat 
        (List.map (fun r -> propagate_fml r b) (CP.list_of_conjs rcase2))) (CP.list_of_conjs bcase)) in
    CP.conj_of_list ([rcase]@rels@pf@(List.concat lp)) no_pos
  with _ -> rcase_orig

(* TODO: Need to handle computed relation in the future *)
let rec get_other_branches or_fml args = match or_fml with
  | Or fml -> 
    (get_other_branches fml.formula_or_f1 args) @ (get_other_branches fml.formula_or_f2 args)
  | _ ->
    let _,p,_,_,a = split_components or_fml in (*TO CHECK: a*)
    let conjs = CP.list_of_conjs (MCP.pure_of_mix p) in
    List.filter (fun pure -> CP.subset args (CP.fv pure)) conjs

(* TODO: Default number of disjs is 1 *)
let propagate_rec pfs rel ante_vars specs = match CP.get_rel_id rel with
  | None -> (pfs,1)
  | Some ivs ->
    let (rcases, bcases) = List.partition is_rec pfs in
    let or_post = get_or_post specs (CP.get_rel_id_list rel) in
    let bcases = 
      begin
      match or_post with
      | [] -> bcases
      | [or_fml] ->
        let other_branches = get_other_branches or_fml (CP.get_rel_args rel) in
        let other_branches = List.map (fun p -> CP.mkNot p None no_pos) other_branches in
        let pure_other_branches = CP.conj_of_list other_branches no_pos in
        List.filter (fun b -> TP.is_sat_raw (MCP.mix_of_pure (CP.mkAnd b pure_other_branches no_pos))) bcases
      | _ -> bcases
      end
    in
(*    let bcases = List.map (fun b -> TP.simplify_raw b) bcases in*)
    let no_of_disjs = List.map (fun b -> let disjs = CP.list_of_disjs b in 
        let cond = List.exists (fun d -> let conjs = CP.list_of_conjs d in 
            List.exists (fun c -> CP.is_eq_const c) conjs) disjs in 
        if cond then 1 else List.length disjs) bcases in 

    (*let no_of_disjs = List.map (fun b -> CP.no_of_disjs b) bcases in*)
    let no_of_disjs = List.fold_left (fun a b -> max a b) 1 no_of_disjs in 

    match bcases with
    | [bcase] -> ([bcase] @ (List.map (fun rcase -> propagate_rec_helper rcase bcase rel ante_vars) rcases), no_of_disjs)
    | _ -> (bcases @ (List.map (fun rcase -> arr_args rcase rel ante_vars) rcases), no_of_disjs)
(*      let new_bcases = remove_weaker_bcase bcases in
      new_bcases @ (List.map (fun rcase -> arr_args rcase rel ante_vars) rcases)*)

let rec compute_fixpoint (i:int) input_pairs pre_vars specs =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  DD.no_2_num i "compute_fixpoint" pr1 pr2 (pr_list (pr_triple pr0 pr0 pr0)) 
      (fun _ _ -> compute_fixpoint_x input_pairs pre_vars specs) input_pairs pre_vars

and compute_fixpoint_x input_pairs ante_vars specs =
(*  let input_pairs_rec = List.map (fun (p,r) -> is_rec p) input_pairs in*)
(*  let is_recur = List.fold_left (||) false input_pairs_rec in*)
  let is_bag_cnt rel =
    let bag_vars = List.filter CP.is_bag_typ (CP.fv rel) in
    bag_vars != []
  in
  let input_pairs_bag, input_pairs_num = List.partition (fun (p,r) -> is_bag_cnt r) input_pairs in
  let bag_res = if input_pairs_bag = [] then [] else Fixbag.compute_fixpoint 3 input_pairs_bag ante_vars true in
  let num_res =
    if input_pairs_num = [] then []
    else
(*    if is_recur then *)
      let (pfs, rels) = List.split input_pairs_num in
      let rels = Gen.BList.remove_dups_eq CP.equalFormula rels in
      let triples = List.concat (List.map (fun r -> helper input_pairs_num r ante_vars specs) rels) in 
      let triples = preprocess_rels triples in
      DD.ninfo_pprint ("input_pairs_num: " ^ (pr_list (pr_pair !CP.print_formula !CP.print_formula) input_pairs_num)) no_pos;
      let rel = List.map (fun (x,y,n) -> (x,y,n,ante_vars)) triples in
      compute_fixpoint_aux rel
(*    else *)
(*      let (pfs, rels) = List.split input_pairs in*)
(*      let rels = Gen.BList.remove_dups_eq CP.equalFormula rels in*)
(*      let res = List.map (fun rel -> *)
(*        let pairs = List.filter (fun (p,r) -> CP.equalFormula r rel) input_pairs in*)
(*        let pfs,_ = List.split pairs in*)
(*        let is_mona = TP.is_bag_constraint (List.hd pfs) in*)
(*        let pfs = if is_mona then *)
(*          List.map (fun p -> *)
(*            let bag_vars = List.filter CP.is_bag_typ (CP.fv p) in*)
(*            CP.remove_cnts bag_vars p) pfs*)
(*          else pfs*)
(*        in*)
(*        let pfs = List.map (fun p -> *)
(*          let exists_vars = CP.diff_svl (CP.fv p) (CP.fv rel) in *)
(*          let exists_vars = List.filter (fun x -> not(CP.is_rel_var x)) exists_vars in*)
(*          TP.simplify_exists_raw exists_vars p) pfs *)
(*        in*)
(*        (rel,List.fold_left (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (CP.mkFalse no_pos) pfs)*)
(*        ) rels*)
(*      in res*)
  in bag_res @ num_res

and preprocess_rels rels =
  match rels with
  | rel::r -> 
    let same_rels, diff_rels = List.partition (fun (x,y,_) -> CP.eq_spec_var (CP.name_of_rel_form x) (CP.name_of_rel_form ((fun(a,_,_)-> a) rel))) r in
    let new_rels = if(same_rels==[]) then [rel] else (unify_rels rel same_rels) in 
    new_rels@(preprocess_rels diff_rels)
  | [] -> []

and unify_rels rel same_rels =
  match rel, same_rels with
  | (CP.BForm ((CP.RelForm (name1,args1,p1),p2),p3), f1,n1), (CP.BForm ((CP.RelForm (name2,args2,_),_),_), f2,n2)::r ->
    let subst_arg = List.combine (List.map CP.exp_to_spec_var args2) (List.map CP.exp_to_spec_var args1) in
    let f2 = CP.subst subst_arg f2 in
    let new_f = CP.Or(f1,f2,None,no_pos) in
    DD.ninfo_pprint ("new rel = " ^ (!CP.print_formula new_f))  no_pos;
    (CP.BForm ((CP.RelForm (name1,args1,p1),p2),p3), new_f,n1)::(unify_rels rel r)
  | (CP.BForm ((CP.RelForm (name1,args1,_),_),_), f1,_), [] -> []
  | _ -> report_error no_pos ("Unexpected format\n") 
	    

and helper input_pairs rel ante_vars specs = 
  let pairs = List.filter (fun (p,r) -> CP.equalFormula r rel) input_pairs in
  let pfs,_ = List.split pairs in
  Debug.ninfo_hprint (add_str "pfs:" (pr_list !CP.print_formula)) pfs no_pos;
  let is_mona = TP.is_bag_constraint (List.hd pfs) in
  let pfs = if is_mona then 
    List.map (fun p -> 
      let p = TP.simplify_raw p in
      let bag_vars = List.filter CP.is_bag_typ (CP.fv p) in
      CP.remove_cnts bag_vars p) pfs
    else pfs
  in
  Debug.ninfo_hprint (add_str "pfs:" (pr_list !CP.print_formula)) pfs no_pos;
  let pfs,no = propagate_rec pfs rel ante_vars specs in
  let pfs = List.map (fun p -> 
    let exists_vars = CP.diff_svl (CP.fv p) (CP.fv rel) in 
    let exists_vars = List.filter (fun x -> not(CP.is_rel_var x)) exists_vars in
    Debug.ninfo_hprint (add_str "p:" !CP.print_formula) p no_pos;
    Debug.ninfo_hprint (add_str "rel:" !CP.print_formula) rel no_pos;
    Debug.ninfo_hprint (add_str "exist vars:" !CP.print_svl) exists_vars no_pos;
    CP.mkExists exists_vars p None None no_pos) pfs 
  in
  match pfs with
  | [] -> []
  | [hd] -> [(rel,hd,no)]
  | _ -> [(rel, List.fold_left (fun p1 p2 -> CP.mkOr p1 p2 None None no_pos) (List.hd pfs) (List.tl pfs), no)]

and compute_fixpoint_aux rel = 
  let no = List.fold_left (fun a b -> max a b) 1 (List.map (fun (_,_,a,_) -> a) rel) in
  let input_fixcalc, fixcalc = 
    if no=1 then
      (List.fold_left (fun x y -> x ^ (compute_fixpoint_one y)) "" rel) ^ (compute_bottomup_inp rel), fixcalc
    else
      List.fold_left (fun x (a,b,c,d) -> x ^ (compute_fixpoint_one (a,b,c,d) ^ 
      "\n\nFix1:=bottomup(" ^ (get_rel_name a) ^ "," ^ (string_of_int c) ^ ",SimHeur);\nFix1;\n")) "" rel, fixcalc_old
  in
  DD.ninfo_pprint ("fixpoint input = " ^ input_fixcalc) no_pos;
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
  DD.ninfo_pprint ("res = " ^ res ^ "\n") no_pos;
  DD.devel_pprint ("Result of fixcalc: " ^ res) no_pos;
  let fixpoint = Parse_fix.parse_fix res in
  DD.devel_hprint (add_str "Result of fixcalc (parsed): " (pr_list !CP.print_formula)) fixpoint no_pos;
  (* match fixpoint with  *)
  (* | [post] ->  *)
  (* 	(match (List.hd rel) with  *)
  (* 	  | (f,_,_) -> [(f, post, CP.mkTrue no_pos)]  *)
  (* 	  | _ -> report_error no_pos "Error") *)
  (* | _ -> report_error no_pos "Expecting a pair of pre-post" *)
 
  let fixpoint_rel = 
    try List.combine fixpoint rel 
    with _ -> report_error no_pos "Error in compute_fixpoint_aux" 
  in
  List.map (fun x ->
	  match x with
    | (post, (rel,_,_,_)) -> (rel, post)
    (*| _ -> report_error no_pos "Expecting a post"*)
	) fixpoint_rel

and compute_fixpoint_one (rel_fml, pf, no, ante_vars) =
(*  if CP.isConstFalse pf then (rel_fml, CP.mkFalse no_pos, CP.mkFalse no_pos) *)
(*  else  *)
  let (name,vars) = match rel_fml with
    | CP.BForm ((CP.RelForm (name,args,_),_),_) -> (CP.name_of_spec_var name, (List.concat (List.map CP.afv args)))
    | _ -> report_error no_pos ("Wrong format: " ^ (!CP.print_formula rel_fml) ^ "\n")
  in
  let pre_vars, post_vars = List.partition (fun v -> List.mem v ante_vars) vars in
  try
    let rhs = fixcalc_of_pure_formula pf in 
    let input_fixcalc =  name ^ ":={[" ^ (string_of_elems pre_vars fixcalc_of_spec_var ",") ^ "] -> "
      ^ "[" ^ (string_of_elems post_vars fixcalc_of_spec_var ",") ^ "] -> []: " 
      ^ rhs ^ "\n};"
    in input_fixcalc
  with _ -> report_error no_pos "Unexpected error in computing fixpoint"

and compute_bottomup_inp rel = 
  if rel!=[] then 
    let first_elm = 
      match (List.hd rel) with 
      | (f,_,_,_) -> (get_rel_name f) 
     (* | _ -> report_error no_pos "Error in computing fixpoint" *)
    in "bottomupgen([" ^  (List.fold_left (fun x (y,_,_,_) -> (x ^ "," ^ (get_rel_name y))) first_elm (List.tl rel)) ^ "]);"
  else report_error no_pos "No relation provided"

and get_rel_name rel = match rel with
 | CP.BForm ((CP.RelForm (name,args,_),_),_) -> CP.name_of_spec_var name
 | _ -> report_error no_pos ("Wrong format: " ^ (!CP.print_formula rel) ^ "\n")
 


