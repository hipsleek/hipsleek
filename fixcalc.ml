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

(******************************************************************************)

let fixcalc = "fixcalc"
let fixcalc = "/home/thaitm/hg-repository/infer-rec/sleekex/bin/fixcalc"
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

(******************************************************************************)

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

(******************************************************************************)

let rec remove_paren s n = if n=0 then "" else match s.[0] with
  | '(' -> remove_paren (String.sub s 1 (n-1)) (n-1)
  | ')' -> remove_paren (String.sub s 1 (n-1)) (n-1)
  | _ -> (String.sub s 0 1) ^ (remove_paren (String.sub s 1 (n-1)) (n-1))

let fv_rel pure = match pure with
  | CP.BForm((CP.RelForm(_,es,_),_),_) -> List.concat (List.map CP.afv es)
  | _ -> []

let rec is_rec pf = match pf with
  | CP.BForm (bf,_) -> CP.is_RelForm pf
  | CP.And (f1,f2,_) -> is_rec f1 || is_rec f2
  | CP.AndList b -> exists_l_snd is_rec b
  | CP.Or (f1,f2,_,_) -> is_rec f1 || is_rec f2
  | CP.Not (f,_,_) -> is_rec f
  | CP.Forall (_,f,_,_) -> is_rec f
  | CP.Exists (_,f,_,_) -> is_rec f

let rec get_rel_vars pf = match pf with
  | CP.BForm (bf,_) -> if CP.is_RelForm pf then fv_rel pf else []
  | CP.And (f1,f2,_) -> get_rel_vars f1 @ get_rel_vars f2
  | CP.AndList b -> fold_l_snd get_rel_vars b
  | CP.Or (f1,f2,_,_) -> get_rel_vars f1 @ get_rel_vars f2
  | CP.Not (f,_,_) -> get_rel_vars f
  | CP.Forall (_,f,_,_) -> get_rel_vars f
  | CP.Exists (_,f,_,_) -> get_rel_vars f

let substitute (e: CP.exp): (CP.exp * CP.formula list) = match e with
  | CP.Var _ -> (e, [])
  | _ -> 
    (try 
      let arb = List.hd (CP.afv e) in 
      let var = CP.fresh_spec_var_prefix "fc" arb in
      let var = CP.mkVar var no_pos in
      (var, [CP.mkEqExp var e no_pos])
    with _ -> (e,[]))

let arr_para_order (rel: CP.formula) (rel_def: CP.formula) 
                   (ante_vars: CP.spec_var list) = 
  match (rel,rel_def) with
  | (CP.BForm ((CP.RelForm (id,args,p), o1), o2), CP.BForm ((CP.RelForm (id_def,args_def,_), _), _)) -> 
    if id = id_def then 
      let new_args_def = 
        let pre_args, post_args = 
          List.partition 
            (fun e -> Gen.BList.subset_eq CP.eq_spec_var (CP.afv e) ante_vars) 
          args_def 
        in
        pre_args @ post_args 
      in
      let pairs = List.combine args_def args in
      let new_args = List.map (fun a -> List.assoc a pairs) new_args_def in
      let new_args, subs = List.split (List.map (fun a -> substitute a) new_args) in
      (CP.BForm ((CP.RelForm (id,new_args,p), o1), o2), 
        [CP.conj_of_list (List.concat subs) no_pos])
    else 
      let args, subs = List.split (List.map (fun a -> substitute a) args) in
      (CP.BForm ((CP.RelForm (id,args,p), o1), o2), [CP.conj_of_list (List.concat subs) no_pos])
  | _ -> report_error no_pos "Expected relation formulas"

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
  let rcase = TP.simplify_raw (CP.drop_rel_formula rcase_orig) in
  let rels = CP.get_RelForm rcase_orig in
  let rels,lp = List.split 
                (List.map (fun r -> arr_para_order r rel ante_vars) rels) in
  let rel_vars = CP.remove_dups_svl (get_rel_vars rcase_orig) in
  let exists_vars = CP.diff_svl (CP.fv rcase) rel_vars in
  let exists_vars = List.filter (fun x -> not(CP.is_rel_var x)) exists_vars in
  try
    let rcase2 = TP.simplify_raw (CP.mkExists exists_vars rcase None no_pos) in
    let pairs = List.combine (fv_rel rel) rel_vars in
    let bcase = CP.subst pairs bcase_orig in
    let pf = List.concat (List.map (fun b -> 
      List.concat (List.map (fun r -> propagate_fml r b) (CP.list_of_conjs rcase2))) 
      (CP.list_of_conjs bcase)) 
    in
    CP.conj_of_list ([rcase]@rels@pf@(List.concat lp)) no_pos
  with _ -> rcase_orig

(* TODO: Need to handle computed relation in the future *)
let rec get_other_branches or_fml args = match or_fml with
  | Or fml -> 
    (get_other_branches fml.formula_or_f1 args) @ 
    (get_other_branches fml.formula_or_f2 args)
  | _ ->
    (* TODO CHECK: a*)
    let _,p,_,_,a = split_components or_fml in 
    let conjs = CP.list_of_conjs (MCP.pure_of_mix p) in
    List.filter (fun pure -> CP.subset args (CP.fv pure)) conjs

let propagate_rec pfs rel ante_vars specs = match CP.get_rel_id rel with
  | None -> report_error no_pos "Expected a relation"
  | Some ivs ->
    let (rcases, bcases) = List.partition is_rec pfs in

    (* TODO *)
    let or_post = get_or_post specs (CP.get_rel_id_list rel) in
    let bcases = 
      begin
      match or_post with
      | [] -> bcases
      | [or_fml] ->
        let other_branches = get_other_branches or_fml (CP.get_rel_args rel) in
        let other_branches = List.map (fun p -> CP.mkNot_s p) other_branches in
        let pure_other_branches = CP.conj_of_list other_branches no_pos in
        List.filter (fun b -> TP.is_sat_raw (MCP.mix_of_pure 
          (CP.mkAnd b pure_other_branches no_pos))) bcases
      | _ -> bcases
      end
    in

    let no_of_disjs = 
      List.map (fun b -> 
        let disjs = CP.list_of_disjs b in 
        (* TODO *)
        let cond = List.exists (fun d -> 
            let conjs = CP.list_of_conjs d in 
            List.exists (fun c -> CP.is_eq_const c) conjs
          ) disjs 
        in 
        if cond then 1 else List.length disjs
      ) bcases 
    in
    let no_of_disjs = List.fold_left (fun a b -> max a b) 1 no_of_disjs in 

    (* TODO: drop rel, simplify and add rel and propagate formula *)
    match bcases with
    | [bcase] -> ([bcase] @ (List.map (fun rcase -> 
      propagate_rec_helper rcase bcase rel ante_vars) rcases), no_of_disjs)
    | _ -> (bcases @ (List.map (fun rcase -> 
                        arr_args rcase rel ante_vars) rcases), no_of_disjs)

let compute_def (rel_fml, pf, no) ante_vars =
  let (name,vars) = match rel_fml with
    | CP.BForm ((CP.RelForm (name,args,_),_),_) -> 
      (CP.name_of_spec_var name, (List.concat (List.map CP.afv args)))
    | _ -> report_error no_pos 
              ("Wrong format: " ^ (!CP.print_formula rel_fml) ^ "\n")
  in

  let pre_vars, post_vars = 
      List.partition (fun v -> List.mem v ante_vars) vars in

  try
    let rhs = fixcalc_of_pure_formula pf in 
    let input_fixcalc =  
        name ^ ":={[" 
      ^ (string_of_elems pre_vars fixcalc_of_spec_var ",") ^ "] -> "
      ^ "[" ^ (string_of_elems post_vars fixcalc_of_spec_var ",") ^ "] -> []: " 
      ^ rhs ^ "\n};"
    in input_fixcalc
  with _ -> report_error no_pos "Error in computing fixpoint"

let compute_cmd rel_defs = 
  let nos = List.map (fun (_,_,a) -> a) rel_defs in
  let nos = string_of_elems nos string_of_int "," in

  let rels = List.map (fun (a,_,_) -> 
                CP.name_of_spec_var (CP.name_of_rel_form a)) rel_defs in
  let names = string_of_elems rels (fun x -> x) "," in

  "\nbottomupgen([" ^ names ^ "], [" ^ nos ^ "], SimHeur);"

let compute_fixpoint_aux rel_defs ante_vars subs = 
  let input_fixcalc = 
    let def = List.fold_left (fun x y -> x ^ (compute_def y ante_vars)) "" rel_defs in
    let cmd = compute_cmd rel_defs in 
    def ^ cmd
  in

  DD.ninfo_pprint ("fixpoint input = " ^ input_fixcalc) no_pos;
  DD.devel_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
  DD.devel_pprint ("Input of fixcalc: " ^ input_fixcalc) no_pos;

  (* Call the fixpoint calculation *)
  let output_of_sleek = "fixcalc.inf" in
  let oc = open_out output_of_sleek in
  Printf.fprintf oc "%s" input_fixcalc;
  flush oc;
  close_out oc;
  let res = syscall (fixcalc ^ " " ^ output_of_sleek) in

  let res = remove_paren res (String.length res) in
  DD.ninfo_pprint ("res = " ^ res ^ "\n") no_pos;

  (* Handle result *)
  DD.devel_pprint ("Result of fixcalc: " ^ res) no_pos;
  let fixpoints = Parse_fix.parse_fix res in
  DD.devel_hprint (add_str "Result of fixcalc (parsed): " 
    (pr_list !CP.print_formula)) fixpoints no_pos;
 
  let rels = List.map (fun (a,_,_) -> a) rel_defs in
  let res = 
    try List.combine rels fixpoints
    with _ -> report_error no_pos "Error in compute_fixpoint_aux"
  in
  DD.ninfo_pprint ("res(b4): " ^ 
    (pr_list (pr_pair !CP.print_formula !CP.print_formula) res)) 
    no_pos;
  let res = List.map (fun (a_rel,fixpoint) -> 
      match a_rel with
      | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->
        let subst_arg = 
          try List.assoc name subs
          with _ -> []
        in
        let subst_arg = List.map (fun (x,y) -> (y,x)) subst_arg in
        if subst_arg = [] then (a_rel, fixpoint)
        else (CP.subst subst_arg a_rel, CP.subst subst_arg fixpoint)
      | _ -> report_error no_pos "Expected a relation"
    ) res in
  DD.ninfo_pprint ("res(af): " ^ 
    (pr_list (pr_pair !CP.print_formula !CP.print_formula) res)) 
    no_pos;
  res

let helper (rel, pfs) ante_vars specs =
  (* Remove bag constraints *)
  Debug.ninfo_hprint (add_str "pfs(b4):" (pr_list !CP.print_formula)) pfs no_pos;
  let pfs = List.map (fun p -> 
      let bag_vars = List.filter CP.is_bag_typ (CP.fv p) in
      if bag_vars == [] then p else 
        let p = TP.simplify_raw p in
        CP.remove_cnts bag_vars p
      ) pfs
  in
  Debug.ninfo_hprint (add_str "pfs(af):" (pr_list !CP.print_formula)) pfs no_pos;

  (* Propagation *)
  let pfs,no = propagate_rec pfs rel ante_vars specs in

  (* Make existence *)
  let pfs = List.map (fun p -> 
    let exists_vars = CP.diff_svl (CP.fv p) (CP.fv rel) in
    let exists_vars = List.filter (fun x -> not(CP.is_rel_var x)) exists_vars in
    CP.mkExists exists_vars p None no_pos) pfs 
  in

  (* disjunctive def *)
  let def = List.fold_left 
          (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (CP.mkFalse no_pos) pfs in
  [(rel, def, no)]
  
let rec unify_rels rel a_rel = match rel, a_rel with
  | (CP.BForm ((CP.RelForm (name1,args1,p1),p2),p3), f1), 
    (CP.BForm ((CP.RelForm (name2,args2,_ ),_ ),_ ), f2) ->
    let subst_arg = List.combine (List.map CP.exp_to_spec_var args2) 
                                 (List.map CP.exp_to_spec_var args1) in
    let f2 = CP.subst subst_arg f2 in
    f2
  | _ -> report_error no_pos ("Unexpected format\n") 

let rec preprocess rels = match rels with
  | [] -> []
  | r::rs -> 
    let rel = snd r in
    let name = CP.name_of_rel_form rel in
    let same_rels, diff_rels = 
      List.partition (fun r0 -> 
        CP.eq_spec_var (CP.name_of_rel_form (snd r0)) name) rs in
    let unified_rels = 
      if same_rels == [] then [(snd r, [fst r])]
      else 
        let res = List.map (fun r0 -> 
                    if CP.equalFormula rel (snd r0) then (fst r0)
                    else unify_rels r r0) same_rels in
        [(snd r, (fst r) :: res)]
    in
    unified_rels @ (preprocess diff_rels)

let arrange_para input_pairs ante_vars =
  let pairs, subs = List.split 
    (List.map (fun (r,pfs) ->
      match r with
      | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->
        let pre_args, post_args = 
          List.partition 
            (fun e -> Gen.BList.subset_eq CP.eq_spec_var (CP.afv e) ante_vars) 
          args
        in
        let new_args = pre_args @ post_args in
        if new_args = args then ((r,pfs),[])
        else
          let subst_arg = List.combine (List.map CP.exp_to_spec_var args) 
                                       (List.map CP.exp_to_spec_var new_args) 
          in
          ((CP.BForm ((CP.RelForm (name,new_args,o1),o2),o3), 
            List.map (fun x -> CP.subst subst_arg x) pfs),[(name,subst_arg)])
      | _ -> report_error no_pos "Expected a relation"
    ) input_pairs)
  in 
  pairs, List.concat subs

let compute_fixpoint_xx input_pairs_num ante_vars specs =
(*  let input_pairs_rec = List.map (fun (p,r) -> is_rec p) input_pairs in*)
(*  let is_recur = List.fold_left (||) false input_pairs_rec in*)
(*    if is_recur then *)
  DD.ninfo_pprint ("input_pairs_num: " ^ 
    (pr_list (pr_pair !CP.print_formula !CP.print_formula) input_pairs_num)) 
    no_pos;

  let pairs = preprocess input_pairs_num in

  DD.ninfo_pprint ("input_pairs(b4): " ^ 
    (pr_list (pr_pair !CP.print_formula (pr_list !CP.print_formula)) pairs)) 
    no_pos;

  let pairs, subs = arrange_para pairs ante_vars in

  DD.ninfo_pprint ("input_pairs(af): " ^ 
    (pr_list (pr_pair !CP.print_formula (pr_list !CP.print_formula)) pairs)) 
    no_pos;

  (* TODO: arrange args of rel and substitute *)
  let rel_defs = List.concat 
    (List.map (fun pair -> helper pair ante_vars specs) pairs) in

  compute_fixpoint_aux rel_defs ante_vars subs

let compute_fixpoint_x input_pairs ante_vars specs =
  let is_bag_cnt rel = List.exists CP.is_bag_typ (CP.fv rel) in
  let input_pairs_bag, input_pairs_num = 
    List.partition (fun (p,r) -> is_bag_cnt r) input_pairs 
  in
  let bag_res = if input_pairs_bag = [] then [] 
    else Fixbag.compute_fixpoint 1 input_pairs_bag ante_vars true 
  in
  let num_res = if input_pairs_num = [] then []
    else compute_fixpoint_xx input_pairs_num ante_vars specs
  in bag_res @ num_res

let compute_fixpoint (i:int) input_pairs ante_vars specs =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  DD.no_2_num i "compute_fixpoint" pr1 pr2 (pr_list (pr_triple pr0 pr0 pr0)) 
    (fun _ _ -> compute_fixpoint_x input_pairs ante_vars specs) 
      input_pairs ante_vars


