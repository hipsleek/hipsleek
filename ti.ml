module CP = Cpure
module CF = Cformula
module MCP = Mcpure

open Cprinter
open Globals
open Gen

(* Auxiliary methods *)
let diff = Gen.BList.difference_eq CP.eq_spec_var

let om_simplify = Omega.simplify

let eq_str s1 s2 = String.compare s1 s2 == 0

let simplify f args = 
  let bnd_vars = diff (CP.fv f) args in
  if bnd_vars == [] then f else
    CP.mkExists_with_simpl om_simplify (* Tpdispatcher.simplify_raw *)
      (diff (CP.fv f) args) f None (CP.pos_of_formula f)
  
let is_sat f = Tpdispatcher.is_sat_raw (MCP.mix_of_pure f)

let mkAnd f1 f2 = CP.mkAnd f1 f2 no_pos

let mkNot f = CP.mkNot f None no_pos

let rec partition_by_key key_of key_eq ls = 
  match ls with
  | [] -> []
  | e::es ->
    let ke = key_of e in 
    let same_es, other_es = List.partition (fun e -> key_eq ke (key_of e)) es in
    (ke, e::same_es)::(partition_by_key key_of key_eq other_es)

(* Temporal Relation at Return *)
type ret_trel = {
  ret_ctx: MCP.mix_formula;
  (* Collect from RHS *)
  termr_fname: ident;
  termr_params: CP.spec_var list;
  termr_lhs: (CP.term_ann * CP.exp list) list;
  termr_rhs: CP.term_ann * CP.exp list;
}

let ret_trel_stk: ret_trel Gen.stack = new Gen.stack

let print_ret_trel rel = 
  string_of_trrel_pure (rel.ret_ctx, rel.termr_lhs, rel.termr_rhs)

let add_ret_trel_stk ctx lhs rhs =
  if !Globals.slk_infer_term then 
    let trel = {
      ret_ctx = ctx;
      termr_fname = CP.get_fn_tann (fst rhs);
      termr_params = List.concat (List.map CP.afv (snd rhs));
      termr_lhs = lhs;
      termr_rhs = rhs; } in 
    ret_trel_stk # push trel
  else ()
  
type trrel_sol = 
  | Base of CP.formula
  | Rec of CP.formula (* Recursive case *)
  | MayTerm of CP.formula (* Both base and rec cases may be reachable from this case *)
  
let print_trrel_sol s = 
  let pr = !CP.print_formula in
  match s with
  | Base c -> (pr c) ^ "@B"
  | Rec c -> (pr c) ^ "@R"
  | MayTerm c -> (pr c) ^ "@ML"

let trans_trrel_sol f = function
  | Base c -> Base (f c)
  | Rec c -> Rec (f c)
  | MayTerm c -> MayTerm (f c)

let fold_trrel_sol f = function
  | Base c -> 
    let cs = f c in
    List.map (fun c -> Base c) cs 
  | Rec c -> 
    let cs = f c in
    List.map (fun c -> Rec c) cs 
  | MayTerm c -> 
    let cs = f c in
    List.map (fun c -> MayTerm c) cs 

let simplify_trrel_sol = trans_trrel_sol om_simplify

let split_disj_trrel_sol s =
  fold_trrel_sol CP.split_disjunctions s
     
let is_base = function
  | Base _ -> true
  | _ -> false

let is_rec = function
  | Rec _ -> true
  | _ -> false

let is_mayterm = function
  | MayTerm _ -> true
  | _ -> false

let get_cond = function
  | Base c -> c
  | Rec c -> c
  | MayTerm c -> c

let get_rec_conds conds = 
  List.map get_cond (List.filter is_rec conds)

let rec solve_rec_trrel rtr conds = 
  let rec_cond = simplify (MCP.pure_of_mix rtr.ret_ctx) rtr.termr_params in
  let rec_cond, conds = List.fold_left (fun (rc, ca) cond ->
    match cond with
    | Base bc -> 
      let oc = mkAnd bc rc in
      if is_sat oc then (* Recursive case and base case are overlapping *)
        let nbc = mkAnd bc (mkNot rc) in
        if is_sat nbc then (mkAnd (mkNot bc) rc, (Base nbc)::(MayTerm oc)::ca)
        else (mkAnd (mkNot bc) rc, (MayTerm oc)::ca)
      else (rc, cond::ca)
    | MayTerm mc -> 
      let oc = mkAnd mc rc in
      if is_sat oc then (mkAnd (mkNot mc) rc, cond::ca)
      else (rc, cond::ca)
    | Rec other_rc ->
      let oc = mkAnd other_rc rc in
      if is_sat oc then 
        let nrc = mkAnd other_rc (mkNot rc) in
        if is_sat nrc then (mkAnd (mkNot other_rc) rc, (Rec oc)::(Rec nrc)::ca)
        else (mkAnd (mkNot other_rc) rc, (Rec oc)::ca)
      else (rc, cond::ca)
  ) (rec_cond, []) conds in
  if is_sat rec_cond then (Rec rec_cond)::conds
  else conds 

let solve_base_trrel btr = 
  Base (simplify (MCP.pure_of_mix btr.ret_ctx) btr.termr_params)

let solve_trrel_list trrels = 
  (* print_endline (pr_list print_ret_trel trrel) *)
  let base_trrels, rec_trrels = List.partition (fun trrel -> trrel.termr_lhs == []) trrels in
  let base_conds = List.map solve_base_trrel base_trrels in
  let conds = List.fold_left (fun conds rtr -> solve_rec_trrel rtr conds) base_conds rec_trrels in 
  let conds = List.map simplify_trrel_sol conds in
  let conds = List.concat (List.map split_disj_trrel_sol conds) in
  conds
  
(* Temporal Relation at Call *)
type call_trel = {
  call_ctx: MCP.mix_formula;
  termu_lhs: CP.term_ann * CP.exp list;
  termu_rhs: CP.term_ann * CP.exp list;
}

let call_trel_stk: call_trel Gen.stack = new Gen.stack

let print_call_trel rel = 
  string_of_turel_pure (rel.call_ctx, rel.termu_lhs, rel.termu_rhs)

let add_call_trel_stk ctx lhs rhs =
  if !Globals.slk_infer_term then 
    let trel = {
      call_ctx = ctx;
      termu_lhs = lhs;
      termu_rhs = rhs; } in 
    call_trel_stk # push trel
  else ()
  
let cantor_pair a b = (a + b) * (a + b + 1) / 2 + b
  
let inst_lhs_trel rel fn_cond_w_ids =  
  let lhs_ann = fst rel.termu_lhs in
  let inst_lhs = match lhs_ann with
    | CP.TermU uid -> 
      let fn = uid.CP.tu_fname in
      let (_, fparams), cond_w_ids = List.find (fun ((fnc, _), _) -> eq_str fn fnc) fn_cond_w_ids in
      let rcond_w_ids = List.filter (fun (_, c) -> is_rec c) cond_w_ids in
      let rcond_w_ids = List.map (fun (i, c) -> (i, get_cond c)) cond_w_ids in
      let tuc = uid.CP.tu_cond in
      let eh_ctx = mkAnd (MCP.pure_of_mix rel.call_ctx) tuc in
      let fs_rconds = List.filter (fun (_, c) -> is_sat (mkAnd eh_ctx c)) rcond_w_ids in
      List.map (fun (i, c) -> CP.TermU { uid with 
        CP.tu_id = cantor_pair uid.CP.tu_id i; 
        CP.tu_cond = mkAnd tuc c; }) fs_rconds
    | _ -> [lhs_ann] 
  in inst_lhs
  
let inst_rhs_trel inst_lhs rel fn_cond_w_ids = 
  let rhs_ann = fst rel.termu_rhs in
  let rhs_args = snd rel.termu_rhs in
  let cond_lhs = CP.get_cond_tann inst_lhs in
  let ctx = mkAnd (MCP.pure_of_mix rel.call_ctx) cond_lhs in
  let inst_rhs = match rhs_ann with
    | CP.TermU uid -> 
      let fn = uid.CP.tu_fname in
      let (_, fparams), cond_w_ids = List.find (fun ((fnc, _), _) -> eq_str fn fnc) fn_cond_w_ids in
      let cond_w_ids = List.map (fun (i, c) -> (i, get_cond c)) cond_w_ids in
      let tuc = uid.CP.tu_cond in
      let eh_ctx = mkAnd ctx tuc in
      let sst = List.combine fparams rhs_args in
      let subst_cond_w_ids = List.map (fun (i, c) -> (i, CP.subst_term_avoid_capture sst c)) cond_w_ids in 
      let fs_rconds = List.filter (fun (_, c) -> is_sat (mkAnd eh_ctx c)) subst_cond_w_ids in
      List.map (fun (i, c) -> CP.TermU { uid with 
        CP.tu_id = cantor_pair uid.CP.tu_id i; 
        CP.tu_cond = mkAnd tuc c; }) fs_rconds
    | _ -> [rhs_ann] 
  in inst_rhs

let inst_call_trel rel fn_cond_w_ids =
  let inst_lhs = inst_lhs_trel rel fn_cond_w_ids in
  let pairs = List.concat (List.map (fun ilhs -> 
    let inst_rhs = inst_rhs_trel ilhs rel fn_cond_w_ids in
    List.map (fun irhs -> (ilhs, irhs)) inst_rhs) inst_lhs) in
  let pr = string_of_term_ann in
  let _ = print_endline (pr_list (pr_pair pr pr) pairs) in
  ()

(* Main Inference Function *)  
let solve () = 
  let _ = print_endline "TERMINATION INFERENCE" in
  let trrels = ret_trel_stk # get_stk in
  let fn_trrels = 
    let key_of r = (r.termr_fname, r.termr_params) in
    let key_eq (k1, _) (k2, _) = String.compare k1 k2 == 0 in  
    partition_by_key key_of key_eq trrels 
  in
  let fn_cond_w_ids = List.map (fun (fn, trrels) -> 
    (fn, List.map (fun c -> fresh_int (), c) (solve_trrel_list trrels))) fn_trrels in
  let _ = 
    let pr_cond (i, c) = "[" ^ (string_of_int i) ^ "]" ^ (print_trrel_sol c) in 
    print_endline ("BASE/REC CASE SPLITTING: \n" ^ 
      (pr_list (fun ((fn, _), s) -> "\t" ^ fn ^ ": " ^ (pr_list pr_cond s) ^ "\n") fn_cond_w_ids)) in
  
  let turels = call_trel_stk # get_stk in
  let irels = List.map (fun rel -> inst_call_trel rel fn_cond_w_ids) turels in
  ()
  
  
  
  