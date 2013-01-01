(*
  Call Fixpoint Calculator for numerical domains
*)

open Globals
open Gen
open Cformula
module DD = Debug
module Pr = Cprinter
module CP = Cpure
module MCP = Mcpure
module TP = Tpdispatcher

(******************************************************************************)

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

(******************************************************************************)

let is_self = CP.is_self_var

let is_null = CP.is_null

let rec string_of_elems elems string_of sep = match elems with 
  | [] -> ""
  | h::[] -> string_of h 
  | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)

(******************************************************************************)

let fixcalc_of_spec_var x = match x with
(*  | CP.SpecVar (Named _, id, Unprimed) -> "NOD" ^ id*)
(*  | CP.SpecVar (Named _, id, Primed) -> "NODPRI" ^ id*)
  | CP.SpecVar (Named _, id, Unprimed)
  | CP.SpecVar (Named _, id, Primed) -> 
    report_error no_pos "Relation contains non-numerical variables"
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
  | CP.Subtract (e1, e2, _) -> 
    fixcalc_of_exp e1 ^ op_sub ^ "(" ^ fixcalc_of_exp e2 ^ ")"
  | CP.Mult (e1, e2, _) -> 
    begin
      match e1, e2 with
      | (CP.IConst (i,_), CP.IConst (j,_)) -> string_of_int (i*j)
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
      if List.exists 
        (fun x -> match x with | CP.IConst _ -> true | _ -> false) args 
      then "0=0"
      else
        (fixcalc_of_spec_var id) ^ "(" ^ 
          (string_of_elems args fixcalc_of_exp ",") ^ ")"
    | _ -> 
      illegal_format ("Fixcalc.fixcalc_of_b_formula: Do not support bag, list")

let rec fixcalc_of_pure_formula f = match f with
  | CP.BForm ((CP.BVar (x,_),_),_,_) -> fixcalc_of_spec_var x ^ op_gt ^ "0"
  | CP.BForm (b,_,_) -> fixcalc_of_b_formula b
  | CP.And (p1, p2, _) ->
    "(" ^ fixcalc_of_pure_formula p1 ^ op_and ^ fixcalc_of_pure_formula p2 ^ ")"
  | CP.AndList b -> 
    (match b with 
    | [] -> fixcalc_of_pure_formula (CP.mkFalse no_pos) 
    | (_,x)::t -> fixcalc_of_pure_formula 
      (List.fold_left (fun a (_,c) -> CP.mkAnd a c no_pos) x t)
    )
  | CP.Or (p1, p2,_ , _) ->
    "(" ^ fixcalc_of_pure_formula p1 ^ op_or ^ fixcalc_of_pure_formula p2 ^ ")"
  | CP.Not (p,_ , _) -> 
    begin
    match p with
    | CP.BForm ((CP.BVar (x,_),_),_,_) -> fixcalc_of_spec_var x ^ op_lte ^ "0"
    | _ -> illegal_format ("Fixcalc.fixcalc_of_pure_formula: 
                            Not supported Not-formula")
    end
  | CP.Forall (sv, p,_ , _) ->
    " (forall (" ^ fixcalc_of_spec_var sv ^ ":" ^ 
                   fixcalc_of_pure_formula p ^ ")) "
  | CP.Exists (sv, p,_ , _) ->
    " (exists (" ^ fixcalc_of_spec_var sv ^ ":" ^ 
                   fixcalc_of_pure_formula p ^ ")) "

let rec fixcalc_of_h_formula f = match f with
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2} -> 
    "(" ^ fixcalc_of_h_formula h1 ^ op_and ^ fixcalc_of_h_formula h2 ^ ")"
  | Phase _ -> 
    illegal_format ("Fixcalc.fixcalc_of_h_formula: Not supported Phase-formula")
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2} -> 
    "(" ^ fixcalc_of_h_formula h1 ^ op_or ^ fixcalc_of_h_formula h2 ^ ")"
  | DataNode {h_formula_data_node = sv; h_formula_data_name = c; 
              h_formula_data_arguments = svs} -> 
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^ (fixcalc_of_spec_var sv) ^ "," ^ 
                   (string_of_elems svs fixcalc_of_spec_var ",") ^ ")"
  | ViewNode {h_formula_view_node = sv; h_formula_view_name = c; 
              h_formula_view_arguments = svs} ->
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^ (fixcalc_of_spec_var sv) ^ "," ^ 
                   (string_of_elems svs fixcalc_of_spec_var ",") ^ ")"
  | HTrue -> "HTrue"
  | HFalse -> "HFalse"
  | HEmp -> "Emp"
  | HRel _ -> "HTrue"
  | Hole _ -> 
    illegal_format ("Fixcalc.fixcalc_of_h_formula: Not supported Hole-formula")

let fixcalc_of_mix_formula f = match f with
  | MCP.MemoF _ -> ""
  | MCP.OnePF pf -> fixcalc_of_pure_formula pf

let rec fixcalc_of_formula e = match e with
  | Or _ -> 
    illegal_format ("Fixcalc.fixcalc_of_formula: Not supported Or-formula")
  | Base {formula_base_heap = h; formula_base_pure = p} ->
    "(" ^ fixcalc_of_h_formula h ^ op_and ^ fixcalc_of_mix_formula p ^ ")"
  | Exists {formula_exists_qvars = svs; formula_exists_heap = h; 
            formula_exists_pure = p} ->     
    " exists (" ^ (string_of_elems svs fixcalc_of_spec_var ",") ^ ": " ^ 
    fixcalc_of_h_formula h ^ op_and ^ fixcalc_of_mix_formula p ^ ")"

(******************************************************************************)

let fixcalc_exe = "/home/thaitm/hg-repository/infer-rec/sleekex/bin/fixcalc "
let fixcalc_exe = "fixcalc "
let fixcalc_options = " -v:-1"
(* to suppress some printing *)

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
      name ^ ":=" ^ "{" ^ "[" ^ self ^ "," ^ 
      (string_of_elems vars fixcalc_of_spec_var ",") ^ "]" ^ " -> [] -> []: " ^
      (string_of_elems fml (fun (c,_)-> fixcalc_of_formula c) op_or) ^
      "\n};\n\nFix1:=bottomupgen([" ^ name ^ "]);\n\n"
    in 
    Printf.fprintf oc "%s" input_fixcalc;
    flush oc;
    close_out oc;
    let res = syscall (fixcalc_exe ^ output_of_sleek ^ fixcalc_options) in
    let new_pf = List.hd (Parse_fix.parse_fix res) in
    let check_imply = Omega.imply new_pf pf "1" 100.0 in
    if check_imply then (
      Pr.fmt_string "INV:  ";
      Pr.pr_angle name 
        (fun x -> Pr.fmt_string (Pr.string_of_typed_spec_var x)) vars;
      Pr.fmt_string ("\nOLD: " ^ (Pr.string_of_pure_formula pf) ^
                     "\nNEW: " ^ (Pr.string_of_pure_formula new_pf) ^ "\n\n");			
      new_pf)
    else pf

(******************************************************************************)

let rec remove_paren s n = if n=0 then "" else match s.[0] with
  | '(' -> remove_paren (String.sub s 1 (n-1)) (n-1)
  | ')' -> remove_paren (String.sub s 1 (n-1)) (n-1)
  | _ -> (String.sub s 0 1) ^ (remove_paren (String.sub s 1 (n-1)) (n-1))

let rec is_rec pf = match pf with
  | CP.BForm (bf,_,_) -> CP.is_RelForm pf
  | CP.And (f1,f2,_) -> is_rec f1 || is_rec f2
  | CP.AndList b -> exists_l_snd is_rec b
  | CP.Or (f1,f2,_,_) -> is_rec f1 || is_rec f2
  | CP.Not (f,_,_) -> is_rec f
  | CP.Forall (_,f,_,_) -> is_rec f
  | CP.Exists (_,f,_,_) -> is_rec f

let substitute_args_x a_rel = match a_rel with
  | CP.BForm ((CP.RelForm (name,args,o1),o2),o3,o4) ->
    let new_args, subs = List.split 
      (List.map (fun e ->
        match e with
        | CP.Var _ -> (e, [])
        | _ -> 
          (try 
            let arb = List.hd (CP.afv e) in 
            let var = CP.fresh_spec_var_prefix "fc" arb in
            let var = CP.mkVar var no_pos in
            (var, [CP.mkEqExp var e no_pos])
          with _ -> (e,[]))
      ) args)
    in
    (CP.BForm ((CP.RelForm (name,new_args,o1),o2),o3,o4), List.concat subs)
  | _ -> report_error no_pos "substitute_args_x Expected a relation"

let substitute_args rcase =
  let rels = CP.get_RelForm rcase in
  let rcase_wo_rel = TP.simplify_raw (CP.drop_rel_formula rcase) in
  let rels, subs = 
    List.split (List.map (fun rel -> substitute_args_x rel) rels) in
  let res = [rcase_wo_rel]@rels@(List.concat subs) in
  CP.conj_of_list res no_pos

(* TODO: Need to handle computed relation in the future *)
let rec get_other_branches or_fml args = match or_fml with
  | Or fml -> 
    (get_other_branches fml.formula_or_f1 args) @ 
    (get_other_branches fml.formula_or_f2 args)
  | _ ->
    (* TODO CHECK: a *)
    let _,p,_,_,a = split_components or_fml in 
    let conjs = CP.list_of_conjs (MCP.pure_of_mix p) in
    List.filter (fun pure -> CP.subset args (CP.fv pure)) conjs

let process_base_rec pfs rel specs = match CP.get_rel_id rel with
  | None -> report_error no_pos "process_base_rec: Expected a relation"
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
      ) bcases in
    let no_of_disjs = List.fold_left (fun a b -> max a b) 1 no_of_disjs in 

    (* Normalize each relation *)
    let rcases = List.map (fun x -> substitute_args x) rcases in

    bcases @ rcases, no_of_disjs
    
let compute_def (rel_fml, pf, no) ante_vars =
  let (name,vars) = match rel_fml with
    | CP.BForm ((CP.RelForm (name,args,_),_),_,_) -> 
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
      ^ (string_of_elems pre_vars fixcalc_of_spec_var ",") ^ "] -> [" 
      ^ (string_of_elems post_vars fixcalc_of_spec_var ",") ^ "] -> []: " 
      ^ rhs ^ "\n};"
    in input_fixcalc
  with _ -> report_error no_pos "Error in translating the input for fixcalc"

let compute_cmd rel_defs = 
  let nos = List.map (fun (_,_,a) -> a) rel_defs in
  (* let nos = string_of_elems nos string_of_int "," in *)
  let nos = string_of_elems nos (fun _ -> 
      string_of_int !Globals.fixcalc_disj) "," in
  let rels = List.map (fun (a,_,_) -> 
                CP.name_of_spec_var (CP.name_of_rel_form a)) rel_defs in
  let names = string_of_elems rels (fun x -> x) "," in
  "\nbottomupgen([" ^ names ^ "], [" ^ nos ^ "], SimHeur);"

let compute_fixpoint_aux rel_defs ante_vars subs = 
  (* Prepare the input for the fixpoint calculation *)
  let input_fixcalc = 
    let def = 
      List.fold_left (fun x y -> x ^ (compute_def y ante_vars)) "" rel_defs in
    let cmd = compute_cmd rel_defs in 
    def ^ cmd
  in

  DD.devel_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
  DD.devel_pprint ("Input of fixcalc: " ^ input_fixcalc) no_pos;
  DD.ninfo_pprint ("fixpoint input = " ^ input_fixcalc) no_pos;

  (* Call the fixpoint calculation *)
  let output_of_sleek = "fixcalc.inf" in
  let oc = open_out output_of_sleek in
  Printf.fprintf oc "%s" input_fixcalc;
  flush oc;
  close_out oc;
  let res = syscall (fixcalc_exe ^ output_of_sleek ^ fixcalc_options) in

  (* Remove parentheses *)
  let res = remove_paren res (String.length res) in
  DD.ninfo_pprint ("res = " ^ res ^ "\n") no_pos;

  (* Parse result *)
  DD.devel_pprint ("Result of fixcalc: " ^ res) no_pos;
  let fixpoints = Parse_fix.parse_fix res in
  DD.devel_hprint (add_str "Result of fixcalc (parsed): " 
    (pr_list !CP.print_formula)) fixpoints no_pos;

  (* Pre-result *)
  let rels = List.map (fun (a,_,_) -> a) rel_defs in
  let res = 
    try List.combine rels fixpoints
    with _ -> report_error no_pos "Error in compute_fixpoint_aux"
  in

  (* Substitute the parameters of each relation to the original ones *)
  DD.ninfo_pprint ("res(b4): " ^ 
    (pr_list (pr_pair !CP.print_formula !CP.print_formula) res)) no_pos;
  let res = 
    List.map (fun (a_rel,fixpoint) -> 
      match a_rel with
      | CP.BForm ((CP.RelForm (name,args,o1),o2),o3,o4) ->
        let subst_arg = 
          try List.assoc name subs
          with _ -> []
        in
        let subst_arg = List.map (fun (x,y) -> (y,x)) subst_arg in
        if subst_arg = [] then (a_rel, fixpoint)
        else (CP.subst subst_arg a_rel, CP.subst subst_arg fixpoint)
      | _ -> report_error no_pos "compute_fixpoint_aux: Expected a relation"
    ) res in
  DD.ninfo_pprint ("res(af): " ^ 
    (pr_list (pr_pair !CP.print_formula !CP.print_formula) res)) no_pos;
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

  (* Some other processes *)
  let pfs,no = process_base_rec pfs rel specs in

  (* Make existence *)
  let pfs = List.map (fun p -> 
    let exists_vars = CP.diff_svl (CP.fv p) (CP.fv rel) in
    let exists_vars = List.filter (fun x -> not(CP.is_rel_var x)) exists_vars in
    CP.mkExists exists_vars p None no_pos) pfs 
  in

  (* Disjunctive defintion for each relation *)
  let def = List.fold_left 
          (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (CP.mkFalse no_pos) pfs in
  [(rel, def, no)]
  
let arrange_para input_pairs ante_vars =
  let pairs, subs = List.split 
    (List.map (fun (r,pfs) ->
      match r with
      | CP.BForm ((CP.RelForm (name,args,o1),o2),o3,o4) ->
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
          ((CP.BForm ((CP.RelForm (name,new_args,o1),o2),o3,o4), 
            List.map (fun x -> CP.subst subst_arg x) pfs),[(name,subst_arg)])
      | _ -> report_error no_pos "arrange_para: Expected a relation"
    ) input_pairs)
  in 
  pairs, List.concat subs

let rec unify_rels rel a_rel = match rel, a_rel with
  | (CP.BForm ((CP.RelForm (name1,args1,p1),p2),p3,p4), f1), 
    (CP.BForm ((CP.RelForm (name2,args2,_ ),_ ), _, _), f2) ->
    let subst_arg = List.combine (List.map CP.exp_to_spec_var args2) 
                                 (List.map CP.exp_to_spec_var args1) in
    let f2 = CP.subst subst_arg f2 in
    f2
  | _ -> report_error no_pos "unify_rels: Expected a relation" 

let rec preprocess pairs = match pairs with
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

let compute_fixpoint_xx input_pairs_num ante_vars specs =
  (* TODO: Handle non-recursive ones separately *)
  DD.ninfo_pprint ("input_pairs_num: " ^ (pr_list 
    (pr_pair !CP.print_formula !CP.print_formula) input_pairs_num)) no_pos;

  let pairs = preprocess input_pairs_num in

  DD.ninfo_pprint ("input_pairs(b4): " ^ (pr_list 
    (pr_pair !CP.print_formula (pr_list !CP.print_formula)) pairs)) no_pos;

  let pairs, subs = arrange_para pairs ante_vars in

  DD.ninfo_pprint ("input_pairs(af): " ^ (pr_list 
    (pr_pair !CP.print_formula (pr_list !CP.print_formula)) pairs)) no_pos;

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


