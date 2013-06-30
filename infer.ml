open Globals
(* module DD = Debug *)
open Gen
open Exc.GTable
open Perm
open Cformula
open Context
open Cpure
open Global_var

module Err = Error
module CP = Cpure
module MCP = Mcpure
module CF = Cformula
module TP = Tpdispatcher
module IF = Iformula
module I = Iast
module IMM = Immutable
module SAU = Sautility


(************************************************)
let keep_dist f = match f with
  | BForm ((Eq(e1,e2,_),_),_) ->  not((eqExp_f eq_spec_var e1 e2) || (is_null e1 && (is_null_const_exp e2)) || ((is_null_const_exp e1) && is_null e2)) 
  | _ -> true

let simplify_conjs f =
  let ls = split_conjunctions f in
  let ls = List.map (simplify_disj_new) ls in
  let ls = List.concat (List.map (split_conjunctions) ls) in
  (* remove x=x *)
  let ls = List.filter keep_dist ls in
  (* remove duplicated conjuncts *)
  let ls = remove_dupl_conj_eq ls in
  (* remove x=x inside inner disjuncts *)
  (* let ls = simplify_disj_list ls in *)
  join_conjunctions ls

let simplify_conjs f =
  Debug.no_1 "simplify_conjs" (!CP.print_formula) (!CP.print_formula) simplify_conjs f 

let simp_lhs_rhs vars (c,lhs,rhs) =
  let ra = CP.pure_ptr_equations lhs in
  let (subs,rest) = CP.simplify_subs ra vars [] in
  let nsubs = CP.norm_subs (rest@subs) in
  let asubs = rest@nsubs in	  
  let n_rhs = (CP.subst asubs rhs) in
  let lhs = (CP.subst asubs lhs) in
  let lhs = simplify_conjs lhs in
  let n_lhs = CP.filter_ante lhs n_rhs in
  (c,n_lhs,n_rhs)

(************************************************)

(* Stack of infer_rel that can be kept across sleek invocations *)
(*  CP.infer_rel_type = (CP.rel_cat * CP.formula * CP.formula)  *)

let pr = !CP.print_formula 
let pr_ty = !CP.Label_Pure.ref_string_of_exp
type fc_type = CP.formula * CP.formula * CP.formula * CP.formula

let fixcalc_rel_stk : fc_type Gen.stack_pr = new Gen.stack_pr (pr_quad pr pr pr pr) (==)

let infer_rel_stk : CP.infer_rel_type Gen.stack_pr = new Gen.stack_pr 
  CP.string_of_infer_rel (==)

let rel_ass_stk : hprel Gen.stack_pr = new Gen.stack_pr 
  Cprinter.string_of_hprel_short (==)

let dump_rel_ass s = 
  DD.info_pprint "==========================================";
  DD.info_pprint (" Relational Assumption "^s);
  DD.info_pprint "==========================================";
  DD.info_pprint (rel_ass_stk # string_of_reverse_log);
  DD.info_pprint "=========================================="

let no_infer estate = (estate.es_infer_vars == [])

let no_infer_rel estate = (estate.es_infer_vars_rel == [])

let no_infer_hp_rel estate = (estate.es_infer_vars_hp_rel == [])

let no_infer_all estate = (estate.es_infer_vars == [] && estate.es_infer_vars_rel == [])

let no_infer_all_all estate = no_infer_all estate && (no_infer_hp_rel estate)
  
let remove_infer_vars_all estate =
  let iv = estate.es_infer_vars in
  let ivr = estate.es_infer_vars_rel in
  ({estate with es_infer_vars=[];es_infer_vars_rel=[];}, iv, ivr) 

let remove_infer_vars_partial estate rt =
  let iv = estate.es_infer_vars in
  let ivr = estate.es_infer_vars_rel in
  if (iv==[] && ivr==[]) then (estate,iv,ivr)
  else 
    let r_iv = CP.diff_svl iv rt in
    let r_ivr = CP.diff_svl ivr rt in
    ({estate with es_infer_vars=r_iv;
        es_infer_vars_rel=r_ivr;}, iv,ivr) 

let remove_infer_vars_partial estate rt =
  let pr1 = !print_entail_state in
  let pr2 = !print_svl in
  Debug.no_2 "remove_infer_vars_partial" pr1 pr2 (pr_triple pr1 pr2 pr2) 
      remove_infer_vars_partial estate rt 

let rec remove_infer_vars_all_ctx ctx =
  match ctx with
    | Ctx estate -> 
          let (es,_,_) = remove_infer_vars_all estate in
          Ctx es
    | OCtx (ctx1, ctx2) -> OCtx (remove_infer_vars_all_ctx ctx1, remove_infer_vars_all_ctx ctx2)

let remove_infer_vars_all_partial_context (a,pc) = 
  (a,List.map (fun (b,c) -> (b,remove_infer_vars_all_ctx c)) pc)

let remove_infer_vars_all_list_context ctx = 
  match ctx with
    | FailCtx _ -> ctx
    | SuccCtx lst -> SuccCtx (List.map remove_infer_vars_all_ctx lst)

let remove_infer_vars_all_list_partial_context lpc = 
  List.map remove_infer_vars_all_partial_context lpc

let restore_infer_vars_ctx iv ivr ctx = 
  let rec helper ctx =
    match ctx with
      | Ctx estate ->
            let n_iv = if iv==[] then  estate.es_infer_vars else iv in
            let n_ivr = if ivr==[] then  estate.es_infer_vars_rel else ivr 
            in Ctx {estate with es_infer_vars=n_iv; es_infer_vars_rel=n_ivr;}
      | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

let rec add_infer_vars_ctx iv ctx = 
  match ctx with
  | Ctx estate -> 
        if iv==[] then ctx
        else Ctx {estate with es_infer_vars = iv @ estate.es_infer_vars;}
  | OCtx (ctx1, ctx2) -> OCtx (add_infer_vars_ctx iv ctx1, add_infer_vars_ctx iv ctx2)

let add_impl_expl_vars_ctx iv ev ctx =
  let rec helper ctx = 
    match ctx with
      | Ctx estate -> Ctx {estate with es_gen_impl_vars = iv@estate.es_gen_impl_vars;
                                       es_gen_expl_vars = ev@estate.es_gen_expl_vars;}
      | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

let add_impl_expl_vars_list_partial_context iv ev (ctx:list_partial_context) =
  List.map (fun (fl,bl) -> (fl, List.map (fun (t,b) -> (t,add_impl_expl_vars_ctx iv ev b)) bl)) ctx

(* let restore_infer_vars_list_partial_context iv ivr (ctx:list_partial_context) = *)
(*   List.map (fun (fl,bl) -> (fl, List.map (fun (t,b) -> (t, restore_infer_vars_ctx iv ivr b)) bl)) ctx *)

(* let restore_infer_vars iv cl = *)
(*   if (iv==[]) then cl *)
(*   else match cl with *)
(*     | FailCtx _ -> cl *)
(*     | SuccCtx lst -> SuccCtx (List.map (restore_infer_vars_ctx iv) lst) *)

let rec get_all_args alias_of_root heap = match heap with
  | ViewNode h -> h.h_formula_view_arguments
  | Star s -> (get_all_args alias_of_root s.h_formula_star_h1) @ (get_all_args alias_of_root s.h_formula_star_h2)
  | Conj c -> (get_all_args alias_of_root c.h_formula_conj_h1) @ (get_all_args alias_of_root c.h_formula_conj_h1)
  | Phase p -> (get_all_args alias_of_root p.h_formula_phase_rd) @ (get_all_args alias_of_root p.h_formula_phase_rw) 
  | _ -> []

let is_inferred_pre_list_context ctx = 
  match ctx with
  | FailCtx _ -> false
  | SuccCtx lst -> List.exists CF.is_inferred_pre_ctx lst

let is_inferred_pre_list_context ctx = 
  Debug.no_1 "is_inferred_pre_list_context"
      !print_list_context string_of_bool
      is_inferred_pre_list_context ctx

(* let rec is_inferred_pre_list_context = match ctx with *)
(*   | Ctx estate -> is_inferred_pre estate  *)
(*   | OCtx (ctx1, ctx2) -> (is_inferred_pre_ctx ctx1) || (is_inferred_pre_ctx ctx2) *)

let collect_pre_heap_list_context ctx = 
  match ctx with
  | FailCtx _ -> []
  | SuccCtx lst -> List.concat (List.map collect_pre_heap lst)

let collect_infer_vars_list_context ctx = 
  match ctx with
  | FailCtx _ -> []
  | SuccCtx lst -> List.concat (List.map collect_infer_vars lst)

let collect_formula_list_context ctx = 
  match ctx with
  | FailCtx _ -> []
  | SuccCtx lst -> List.concat (List.map collect_formula lst)

let collect_pre_heap_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c) -> collect_pre_heap c) cl))  ctx in
  List.concat r

let collect_infer_vars_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c) -> collect_infer_vars c) cl))  ctx in
  List.concat r

let collect_formula_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c) -> collect_formula c) cl))  ctx in
  List.concat r

let collect_pre_pure_list_context ctx = 
  match ctx with
  | FailCtx _ -> []
  | SuccCtx lst -> List.concat (List.map collect_pre_pure lst)

let collect_pre_pure_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c) -> collect_pre_pure c) cl))  ctx in
  List.concat r

let collect_rel_list_context ctx = 
  match ctx with
  | FailCtx _ -> []
  | SuccCtx lst -> List.concat (List.map collect_rel lst)

let collect_hp_rel_list_context ctx = 
  match ctx with
  | FailCtx _ -> []
  | SuccCtx lst -> List.concat (List.map collect_hp_rel lst)

let collect_rel_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c) -> collect_rel c) cl))  ctx in
  List.concat r

let collect_rel_list_partial_context (ctx:list_partial_context) =
  let pr1 = !CF.print_list_partial_context in
  let pr2 = pr_list print_lhs_rhs in
  Debug.no_1 "collect_rel_list_partial_context"  pr1 pr2
      collect_rel_list_partial_context ctx

let collect_hp_rel_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c) -> collect_hp_rel c) cl))  ctx in
  List.concat r

let collect_hp_rel_list_partial_context (ctx:list_partial_context) =
  let pr1 = !CF.print_list_partial_context in
  let pr2 =  Cprinter.string_of_hp_rels in
  Debug.no_1 "collect_hp_rel_list_partial_context"  pr1 pr2
      collect_hp_rel_list_partial_context ctx

let collect_hp_unk_map_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c) -> collect_hp_unk_map c) cl))  ctx in
  List.concat r

let init_vars ctx infer_vars iv_rel v_hp_rel orig_vars = 
  let rec helper ctx = 
    match ctx with
      | Ctx estate -> Ctx {estate with es_infer_vars = infer_vars; es_infer_vars_rel = iv_rel;
          es_infer_vars_hp_rel = v_hp_rel;}
      | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

(* let conv_infer_heap hs = *)
(*   let rec helper hs h = match hs with *)
(*     | [] -> h *)
(*     | x::xs ->  *)
(*       let acc =  *)
(* 	    Star({h_formula_star_h1 = x; *)
(* 	      h_formula_star_h2 = h; *)
(* 	      h_formula_star_pos = no_pos}) *)
(*         in helper xs acc in *)
(*   match hs with *)
(*     | [] -> HTrue  *)
(*     | x::xs -> helper xs x *)

(* let extract_pre_list_context x =  *)
(*   (\* TODO : this has to be implemented by extracting from es_infer_* *\) *)
(*   (\* print_endline (!print_list_context x); *\) *)
(*   None *)

let to_unprimed_data_root aset h =
  let r = h.h_formula_data_node in
  if CP.is_primed r then
    let alias = CP.EMapSV.find_equiv_all r aset in
    let alias = List.filter (CP.is_unprimed) alias in
    (match alias with
      | [] -> h
      | (ur::_) -> {h with h_formula_data_node = ur})
  else h

let to_unprimed_view_root aset h =
  let r = h.h_formula_view_node in
  if CP.is_primed r then
    let alias = CP.EMapSV.find_equiv_all r aset in
    let alias = List.filter (CP.is_unprimed) alias in
    (match alias with
      | [] -> h
      | ur::_ -> {h with h_formula_view_node = ur})
  else h

(* get exactly one root of h_formula *)
let get_args_h_formula aset (h:h_formula) =
  let av = CP.fresh_spec_var_ann () in
  match h with
    | DataNode h -> 
          let h = to_unprimed_data_root aset h in
          let root = h.h_formula_data_node in
          let arg = h.h_formula_data_arguments in
          let new_arg = CP.fresh_spec_vars_prefix "inf" arg in
          if (!Globals.allow_imm) then
            Some (root, arg,new_arg, [av],
            DataNode {h with h_formula_data_arguments=new_arg;
              h_formula_data_imm = mkPolyAnn av})
          else
            Some (root, arg,new_arg, [],
            DataNode {h with h_formula_data_arguments=new_arg})
    | ViewNode h -> 
          let h = to_unprimed_view_root aset h in
          let root = h.h_formula_view_node in
          let arg = h.h_formula_view_arguments in
          let new_arg = CP.fresh_spec_vars_prefix "inf" arg in
          if (!Globals.allow_imm) then
            Some (root, arg,new_arg, [av],
            ViewNode {h with h_formula_view_arguments=new_arg; 
              h_formula_view_imm = mkPolyAnn av} )
          else
            Some (root, arg,new_arg, [],
            ViewNode {h with h_formula_view_arguments=new_arg})
    | _ -> None

(*

  Cformula.h_formula ->
  (Cformula.CP.spec_var * Cformula.CP.spec_var list * CP.spec_var list *
   CP.spec_var list * Cformula.h_formula)
  option

*)

let get_args_h_formula aset (h:h_formula) =
  let pr1 = !print_h_formula in
  let pr2 = pr_option (pr_penta !print_sv !print_svl !print_svl !print_svl pr1) in
  Debug.no_1 "get_args_h_formula" pr1 pr2 (fun _ -> get_args_h_formula aset h) h

let get_alias_formula (f:CF.formula) =
  let (h, p, fl, t, a) = split_components f in
  let eqns = (MCP.ptr_equations_without_null p) in
  eqns

(* let get_alias_formula (f:CF.formula) = *)
(*   Debug.no_1 "get_alias_formula" !print_formula !print_pure_f get_alias_formula f *)

let build_var_aset lst = CP.EMapSV.build_eset lst

let is_elem_of conj conjs =
 (* let filtered = List.filter (fun c -> TP.imply_raw conj c && TP.imply_raw c conj) conjs in *)
  let filtered = List.filter (fun c -> CP.equalFormula conj c) conjs in
  match filtered with
    | [] -> false
    | _ -> true

let is_elem_of conj conjs = 
  let pr = !CP.print_formula in
  Debug.no_1 "is_elem_of" pr pr_no (fun _ -> is_elem_of conj conjs) conj

            (* (b,args,inf_arg,h,new_iv,over_iv,[orig_r]) in *)
            (* (List.exists (CP.eq_spec_var_aset lhs_aset r) *)
            (*    iv,args,inf_arg,h,new_iv,over_iv,[r]) in *)
            (* let args_al = List.map (fun v -> CP.EMapSV.find_equiv_all v rhs_aset) args in *)
(* (\* let _ = print_endline ("LHS aliases: "^(pr_list (pr_pair !print_sv !print_sv) lhs_als)) in *\) *)
(* (\* let _ = print_endline ("RHS aliases: "^(pr_list (pr_pair !print_sv !print_sv) rhs_als)) in *\) *)
(* let _ = print_endline ("root: "^(pr_option (fun (r,_,_,_) -> !print_sv r) rt)) in *)
(* let _ = print_endline ("rhs node: "^(!print_h_formula rhs)) in *)
(* let _ = print_endline ("renamed rhs node: "^(!print_h_formula new_h)) in *)
(* (\* let _ = print_endline ("heap args: "^(!print_svl args)) in *\) *)
(* (\* let _ = print_endline ("heap inf args: "^(!print_svl inf_vars)) in *\) *)
(* (\* let _ = print_endline ("heap arg aliases: "^(pr_list !print_svl args_al)) in *\) *)
(* let _ = print_endline ("root in iv: "^(string_of_bool b)) in *)
(* (\* let _ = print_endline ("RHS exist vars: "^(!print_svl es.es_evars)) in *\) *)
(* (\* let _ = print_endline ("RHS impl vars: "^(!print_svl es.es_gen_impl_vars)) in *\) *)
(* (\* let _ = print_endline ("RHS expl vars: "^(!print_svl es.es_gen_expl_vars)) in *\) *)
(* (\* let _ = print_endline ("imm pure stack: "^(pr_list !print_mix_formula es.es_imm_pure_stk)) in *\) *)

(* let aux_test () = *)
(*       DD.trace_pprint "hello" no_pos *)
(* let aux_test () = *)
(*       Debug.no_1_loop "aux_test" pr_no pr_no aux_test () *)
(* let aux_test2 () = *)
(*       DD.trace_pprint "hello" no_pos *)
(* let aux_test2 () = *)
(*       Debug.no_1_num 13 "aux_test2" pr_no pr_no aux_test2 () *)

let infer_heap_nodes (es:entail_state) (rhs:h_formula) rhs_rest conseq pos = 
  if no_infer es then None
  else 
    let iv = es.es_infer_vars in
    let dead_iv = es.es_infer_vars_dead in
    let lhs_als = get_alias_formula es.es_formula in
    let lhs_aset = build_var_aset lhs_als in
    let rt = get_args_h_formula lhs_aset rhs in
    (* let _ = aux_test() in *)
    (* let _ = aux_test2() in *)
    (*  let rhs_als = get_alias_formula conseq in *)
    (*  let rhs_aset = build_var_aset rhs_als in *) 
    match rt with 
      | None -> None
      | Some (orig_r,args,inf_arg,inf_av,inf_rhs) -> 
            (* let (b,args,inf_vars,new_h,new_iv,iv_alias,r) = match rt with (\* is rt captured by iv *\) *)
            (*   | None -> (false,[],[],HTrue,iv,[],[]) *)
            (*   | Some (orig_r,args,inf_arg,inf_av,h) ->  *)
            let alias = CP.EMapSV.find_equiv_all orig_r lhs_aset in
            let rt_al = [orig_r]@alias in (* set of alias with root of rhs *)
            let over_dead = CP.intersect dead_iv rt_al in
            let iv_alias = CP.intersect iv rt_al in 
            let b = (over_dead!=[] || iv_alias == []) in (* does alias of root intersect with iv? *)
            (* let new_iv = (CP.diff_svl (inf_arg@iv) rt_al) in *)
            (* let alias = if List.mem orig_r iv then [] else alias in *)
            if b then None
            else 
              begin
                let new_iv = inf_av@inf_arg@iv in
                (* Take the alias as the inferred pure *)
                (* let iv_al = CP.intersect iv iv_alias in (\* All relevant vars of interest *\) *)
                (* let iv_al = CP.diff_svl iv_al r in *)
                (* iv_alias certainly has one element *)
                let new_r = List.hd iv_alias in
                (* each heap node may only be instantiated once *)
                (* let new_iv = diff_svl new_iv [new_r] in *)
                (* above cause incompleteness in 3.slk (29) & (30). *)
                let new_h = 
                  if CP.eq_spec_var orig_r new_r 
                  then inf_rhs
                  else 
                    (* replace with new root name *)
                    set_node_var new_r inf_rhs 
                in
                let lhs_h,_,_,_,_ = CF.split_components es.es_formula in
                DD.devel_pprint ">>>>>> infer_heap_nodes <<<<<<" pos;
                DD.devel_hprint (add_str "unmatch RHS : " !print_h_formula) rhs pos;
                DD.devel_hprint (add_str "orig inf vars : " !print_svl) iv pos;
                DD.devel_hprint (add_str "inf LHS heap:" !print_h_formula) new_h pos;
                DD.devel_hprint (add_str "new inf vars: " !print_svl) new_iv pos;
                DD.devel_hprint (add_str "dead inf vars: " !print_svl) iv_alias pos;
                (* DD.devel_hprint (add_str "new pure add: " !CP.print_formula) new_p pos; *)
                let r = {
                    match_res_lhs_node = new_h;
                    match_res_lhs_rest = lhs_h;
                    match_res_holes = [];
                    match_res_type = Root;
                    match_res_rhs_node = rhs;
                    match_res_rhs_rest = rhs_rest;
                } in
                let act = M_match r in
                (
                    (* WARNING : any dropping of match action must be followed by pop *)
                    must_action_stk # push act;
                    Some (new_iv,new_h,iv_alias))
              end


(*
type: Cformula.entail_state ->
  Cformula.h_formula ->
  Cformula.h_formula ->
  'a -> (Cformula.CP.spec_var list * Cformula.h_formula) option
*)
let infer_heap_nodes (es:entail_state) (rhs:h_formula) rhs_rest conseq pos = 
  let pr1 = !print_entail_state_short in
  let pr2 = !print_h_formula in
  let pr3 = pr_option (pr_triple !print_svl pr2 !print_svl) in
  Debug.no_2 "infer_heap_nodes" pr1 pr2 pr3
      (fun _ _ -> infer_heap_nodes es rhs rhs_rest conseq pos) es rhs

(* TODO : this procedure needs to be improved *)
(* picks ctr from f that are related to vars *)
(* may involve a weakening process *)
let rec filter_var f vars = 
  match f with
  | CP.Or (f1,f2,l,p) -> 
        CP.Or (filter_var f1 vars, filter_var f2 vars, l, p)
  | _ -> if TP.is_sat_raw (MCP.mix_of_pure f) && CP.get_Neg_RelForm f = [] then CP.filter_var (CP.drop_rel_formula f) vars else CP.mkFalse no_pos
(*        let flag = TP.is_sat_raw f                                 *)
(*          try                                                      *)
(*            Omega.is_sat_weaken f "0"                              *)
(*          with _ -> true                                           *)
(*              (* spurious pre inf when set to true; check 2c.slk *)*)
(*        in
        if flag
        then CP.filter_var f vars 
        else CP.mkFalse no_pos*)

let filter_var f vars =
  let pr = !print_pure_f in
  Debug.no_2 "i.filter_var" pr !print_svl pr filter_var f vars 

let simplify_helper f = match f with
  | BForm ((Neq _,_),_) -> f
  | Not _ -> f
  | _ -> TP.simplify_raw f

(* TODO : this simplify could be improved *)
let simplify f vars = TP.simplify_raw (filter_var (TP.simplify_raw f) vars)
let simplify_contra f vars = filter_var f vars

let simplify f vars =
  let pr = !print_pure_f in
  Debug.no_2 "i.simplify" pr !print_svl pr simplify f vars 

let helper fml lhs_rhs_p weaken_flag = 
  let new_fml = CP.remove_dup_constraints (CP.mkAnd fml lhs_rhs_p no_pos) in
  if TP.is_sat_raw (MCP.mix_of_pure new_fml) then (
    if weaken_flag then fml
    else
      let args = CP.fv new_fml in
      let iv = CP.fv fml in
      let quan_var = CP.diff_svl args iv in
      CP.mkExists_with_simpl TP.simplify_raw quan_var new_fml None no_pos)
  else CP.mkFalse no_pos

let rec simplify_disjs pf lhs_rhs weaken_flag =
  match pf with
  | BForm _ -> if CP.isConstFalse pf then pf else helper pf lhs_rhs weaken_flag
  | And _ -> helper pf lhs_rhs weaken_flag
  | Or (f1,f2,l,p) -> mkOr (simplify_disjs f1 lhs_rhs true) (simplify_disjs f2 lhs_rhs true) l p
  | Forall (s,f,l,p) -> Forall (s,simplify_disjs f lhs_rhs weaken_flag,l,p)
  | Exists (s,f,l,p) -> Exists (s,simplify_disjs f lhs_rhs weaken_flag,l,p)
  | _ -> pf

let simplify_disjs pf lhs_rhs = simplify_disjs pf lhs_rhs false

let infer_lhs_contra pre_thus lhs_xpure ivars pos msg =
  if ivars==[] then None 
  else 
(*  let lhs_xpure_orig = MCP.pure_of_mix lhs_xpure in*)
(*  let lhs_xpure = CP.drop_rel_formula lhs_xpure_orig in*)
(*  let check_sat = TP.is_sat_raw lhs_xpure in*)
  let lhs_xpure_orig = lhs_xpure in
  let lhs_xpure = MCP.mix_drop_rel lhs_xpure_orig in
  let check_sat = TP.is_sat_raw lhs_xpure in
  if not(check_sat) then None
  else 
    let f = simplify_contra (MCP.pure_of_mix lhs_xpure) ivars in
    let vf = CP.fv f in
    let over_v = CP.intersect vf ivars in
    if (over_v ==[]) then None
    else 
      let exists_var = CP.diff_svl vf ivars in
      let f = simplify_helper (CP.mkExists exists_var f None pos) in
      if CP.isConstTrue f || CP.isConstFalse f then None
      else 
        let _ = DD.ninfo_hprint (add_str "f: " !print_formula) f pos in
        let f = TP.pairwisecheck_raw f in
        let neg_f = Redlog.negate_formula f in
        (* Thai: Remove disjs contradicting with pre_thus *)
        let new_neg_f = 
          if CP.isConstTrue pre_thus then neg_f
          else simplify_disjs neg_f pre_thus
(*        let b = if CP.isConstTrue pre_thus then false
          else let f = CP.mkAnd pre_thus neg_f no_pos in
               not(TP.is_sat_raw f) *)
        in
        DD.devel_pprint ">>>>>> infer_lhs_contra <<<<<<" pos; 
        DD.devel_hprint (add_str "trigger cond   : " pr_id) msg pos; 
        DD.devel_hprint (add_str "LHS pure       : " !print_mix_formula) lhs_xpure_orig pos; 
        DD.devel_hprint (add_str "ovrlap inf vars: " !print_svl) over_v pos; 
        DD.devel_hprint (add_str "pre infer   : " !print_formula) neg_f pos; 
        DD.devel_hprint (add_str "new pre infer   : " !print_formula) new_neg_f pos; 
        DD.devel_hprint (add_str "pre thus   : " !print_formula) pre_thus pos; 

        if CP.isConstFalse new_neg_f then
          (DD.devel_pprint "contradiction in inferred pre!" pos; 
          None)
        else Some (new_neg_f)

(*        DD.devel_hprint (add_str "contradict?: " string_of_bool) b pos; 
        if b then
          (DD.devel_pprint "contradiction in inferred pre!" pos; 
          None)
        else Some (neg_f)*)

let infer_lhs_contra pre_thus f ivars pos msg =
  let pr = !print_mix_formula in
  let pr2 = !print_pure_f in
  Debug.no_2 "infer_lhs_contra" pr !print_svl (pr_option pr2) 
      (fun _ _ -> infer_lhs_contra pre_thus f ivars pos msg) f ivars

let infer_lhs_contra_estate estate lhs_xpure pos msg =
  if no_infer_all estate then 
    (None,[])
  else 
    let lhs_pure = MCP.pure_of_mix lhs_xpure in
    let cl = CP.split_conjunctions lhs_pure in
    let (lhs_rel, lhs_wo_rel) = 
      List.partition (fun d -> (CP.get_RelForm d) != [] ) cl in
    let ivs = estate.es_infer_vars_rel in
    let lhs_rel = 
      List.filter (fun d -> (CP.intersect (CP.fv d) ivs) != [] ) lhs_rel in
    let lhs_rels,xp = match lhs_rel with 
      | [] -> None, join_conjunctions lhs_wo_rel
      | _ -> Debug.trace_hprint (add_str "infer_lhs_contra_estate: lhs_rels" (pr_list !CP.print_formula)) lhs_rel no_pos;
            let v = join_conjunctions lhs_rel in
            Some v, join_conjunctions (v::lhs_wo_rel)
    in
    if no_infer estate && lhs_rels = None then (None,[])
    else
      let ivars = estate.es_infer_vars in
      let p_thus = estate.es_infer_pure_thus in
      let r = infer_lhs_contra p_thus lhs_xpure ivars pos msg in
      match r with
        | None -> 
          begin
          match lhs_rels with
            | Some f ->
              DD.devel_pprint ">>>>>> infer_lhs_contra_estate <<<<<<" pos;
              DD.devel_pprint "Add relational assumption" pos;
              let (vs_rel,vs_lhs) = List.partition CP.is_rel_var (CP.fv f) in
              let rel_ass = infer_lhs_contra p_thus lhs_xpure vs_lhs pos "relational assumption" in
              let _ = DD.devel_hprint (add_str "rel_ass(unsat) : " (pr_opt !CP.print_formula)) rel_ass pos in
              begin
                match rel_ass with
                | None -> (None, [])
                | Some neg_lhs ->
                  if (CP.fv neg_lhs == []) then (None,[])
                  else 
                    let rel_ass = 
                      if List.length (List.concat (List.map CP.get_rel_id_list (CP.list_of_conjs f)))=1 then
                        [RelAssume vs_rel,f,neg_lhs]
                      else
                        List.concat (List.map (fun x -> 
                          let lhs_conjs = List.filter (fun y -> 
                            CP.intersect (CP.fv y) (CP.fv x) != []) (CP.list_of_conjs f) in
                          let rel_ids = List.concat (List.map get_rel_id_list lhs_conjs) in
                          if CP.remove_dups_svl rel_ids = rel_ids then
                            [RelAssume vs_rel,CP.conj_of_list lhs_conjs pos,x]
                          else []
                        ) (CP.list_of_conjs neg_lhs)) in
                      if rel_ass = [] then (None,[])
                      else
                        let _ = DD.devel_hprint (add_str "rel_ass_final(unsat) : " (pr_list print_lhs_rhs)) rel_ass pos in
                        let new_estate = CF.false_es_with_orig_ante estate estate.es_formula pos in
                        (None, [(new_estate,rel_ass,true)])
                end
            | None -> (None,[])
          end
        | Some pf ->
            (* let prev_inf_h = estate.es_infer_heap in *)
            (* let prev_inf_p = estate.es_infer_pure in *)
            (* let _ = print_endline ("\nprev inf heap:"^(pr_list !print_h_formula prev_inf_h)) in *)
            (* let _ = print_endline ("prev inf pure:"^(pr_list !CP.print_formula prev_inf_p)) in *)
            let new_estate = CF.false_es_with_orig_ante estate estate.es_formula pos in
            (Some (new_estate,pf),[])

let infer_lhs_contra_estate i e f pos msg =
  let pr0 = !print_entail_state_short in
  let pr = !print_mix_formula in
  let pr2 = fun (_,r,_) -> pr_list pr_none r in
  let pr_res = pr_pair (pr_option (pr_pair pr0 !CP.print_formula)) (pr_list pr2) in
    (* (fun l -> (string_of_int (List.length l))) *)
  Debug.no_2_num i "infer_lhs_contra_estate" pr0 pr pr_res (fun _ _ -> infer_lhs_contra_estate e f pos msg) e f

(*
   should this be done by ivars?
   (i) (lhs & rhs contradict)
       lhs & rhs --> false 
       find a lhs to negate to make state false
   (ii) rhs --> lhs (rhs is stronger)
        find a stronger rhs to add to lhs
*)
(* let infer_lhs_rhs_pure lhs_simp rhs_simp ivars (\* evars *\) = *)
(*   if ivars ==[] then None *)
(*   else  *)
(*     let fml = CP.mkAnd lhs_simp rhs_simp no_pos in *)
(*     let check_sat = Omega.is_sat fml "0" in *)
(*     if not(check_sat) then *)
(*       (\* lhs & rhs |- false *\) *)
(*       let f = simplify lhs_simp ivars in *)
(*       let vf = CP.fv f in *)
(*       let over_v = CP.intersect vf ivars in *)
(*       if (over_v ==[]) then None *)
(*       else Some (Redlog.negate_formula f) *)
(*     else  *)
(*       (\* rhs -> lhs *\) *)
(*       None *)

(* let infer_lhs_rhs_pure lhs rhs ivars = *)
(*   let pr = !print_pure_f in *)
(*   Debug.no_3 "infer_lhs_rhs_pure" pr pr !print_svl (pr_option pr) infer_lhs_rhs_pure lhs rhs ivars *)

(* let infer_lhs_rhs_pure_es estate lhs_xpure rhs_xpure pos = *)
(*   let ivars = estate.es_infer_vars in *)
(*   if ivars == [] then None *)
(*   else  *)
(*     let lhs_xpure = MCP.pure_of_mix lhs_xpure in *)
(*     let rhs_xpure = MCP.pure_of_mix rhs_xpure in *)
(*     let lhs_simp = simplify lhs_xpure ivars in *)
(*     let rhs_simp = simplify rhs_xpure ivars in *)
(*     let r = infer_lhs_rhs_pure lhs_simp rhs_simp ivars in *)
(*     match r with *)
(*       | None -> None *)
(*       | Some pf -> *)
(*             let new_estate = *)
(*               {estate with  *)
(*                   es_formula = normalize 0 estate.es_formula (CF.formula_of_pure_formula pf pos) pos; *)
(*                   es_infer_pure = estate.es_infer_pure@[pf]; *)
(*               } in *)
(*             Some new_estate *)

let present_in (orig_ls:CP.formula list) (new_pre:CP.formula) : bool =
  (* not quite needed, it seems *)
  (* let disj_p = CP.split_disjunctions new_pre in *)
  (* List.exists (fun a -> List.exists (CP.equalFormula a) disj_p) orig_ls *)
  List.exists (fun fml -> TP.imply_raw fml new_pre) orig_ls

let detect_lhs_rhs_contra_x (*lhs_xpure*) lhs_xpure_orig rhs_xpure pos =
      (* let lhs_xpure = MCP.pure_of_mix lhs_xpure_orig in *)
      (* let rhs_vars = CP.fv rhs_xpure in *)
      (* below will help greatly reduce the redundant information inferred from state *)
      (* let lhs_xpure = CP.filter_ante lhs_xpure rhs_xpure in *)
      (* let rhs_xpure = MCP.pure_of_mix rhs_xpure_orig in  *)
      (* let lhs_xpure = MCP.pure_of_mix lhs_xpure0 in  *)
      let split_rhs = CP.split_conjunctions rhs_xpure in
      let rem_rhs = List.filter (fun c -> not(TP.imply_raw lhs_xpure_orig c)) split_rhs in
      let rhs_xpure = CP.join_conjunctions rem_rhs in
      (*let _ = DD.tinfo_hprint (add_str "lhs_xpure: " (!CP.print_formula)) lhs_xpure pos in*)
      let _ = DD.tinfo_hprint (add_str "split_rhs: " (pr_list !CP.print_formula)) split_rhs pos in
      let _ = DD.tinfo_hprint (add_str "rem_rhs: " (pr_list !CP.print_formula)) rem_rhs pos in
      let _ = DD.trace_hprint (add_str "lhs(orig): " !CP.print_formula) lhs_xpure_orig pos in
      (* let _ = DD.trace_hprint (add_str "lhs0(orig): " !print_mix_formula) lhs_xpure0 pos in *)
      let _ = DD.trace_hprint (add_str "rhs(orig): " !CP.print_formula) rhs_xpure pos in
      let lhs_xpure = CP.filter_ante lhs_xpure_orig rhs_xpure in
      let _ = DD.trace_hprint (add_str "lhs (after filter_ante): " !CP.print_formula) lhs_xpure pos in
      let fml = CP.mkAnd lhs_xpure rhs_xpure pos in
      let fml = CP.drop_rel_formula fml in
      (*      let iv_orig = estate.es_infer_vars in*)
      (* let iv_lhs_rel = match lhs_rels with *)
      (*   | None -> [] *)
      (*   | Some f -> List.filter (fun x -> not(is_rel_var x)) (CP.fv f) in *)
      (* Debug.trace_hprint (add_str "iv_orig" !CP.print_svl) iv_orig no_pos; *)
      (* Debug.trace_hprint (add_str "iv_lhs_rel" !CP.print_svl) iv_lhs_rel no_pos; *)
      (* let iv = iv_orig(\* @iv_lhs_rel *\) in *)
      let _ = DD.trace_hprint (add_str "fml: " !CP.print_formula) fml pos in
      let check_sat = TP.is_sat_raw (MCP.mix_of_pure fml) in
      check_sat,fml

let detect_lhs_rhs_contra lhs rhs pos =
	let pr = !CP.print_formula in
	Debug.no_2 "detect_lhs_rhs_contra" pr pr (pr_pair string_of_bool (fun _->"")) 
		(fun _ _ -> detect_lhs_rhs_contra_x lhs rhs pos) lhs rhs
	  
(* let infer_h prog estate conseq lhs_b rhs_b lhs_rels*)

(* lhs_rel denotes rel on LHS where rel assumption be inferred *)
let rec infer_pure_m_x unk_heaps estate lhs_rels lhs_xpure_orig lhs_xpure0 lhs_wo_heap_orig rhs_xpure_orig iv_orig pos =
  (* Debug.info_hprint (add_str "iv_orig" (pr_list pr_none)) iv_orig no_pos;  *)
  (* Debug.info_hprint (add_str "lhs_res" (pr_option pr_none)) lhs_rels no_pos;  *)
  (* Debug.info_hprint (add_str "unk_heaps" (pr_list !CF.print_h_formula)) unk_heaps no_pos;  *)
  if (iv_orig)==[] && unk_heaps==[] && ((no_infer_all_all estate) || (lhs_rels==None)) 
  then 
    (* let _ = Debug.info_pprint "exit" no_pos in *)
    (None,None,[])
  else
    if not (TP.is_sat_raw rhs_xpure_orig) then 
      (* (DD.devel_pprint "Cannot infer a precondition: RHS contradiction" pos; *)
      (* (None,None,[])) *)
      let p, rel_ass = infer_lhs_contra_estate 1 estate lhs_xpure0 pos "rhs contradiction" in
      (p,None,rel_ass)
    else
      let iv = iv_orig(* @iv_lhs_rel *) in
      let lhs_xpure = MCP.pure_of_mix lhs_xpure0 in 
      let rhs_xpure = MCP.pure_of_mix rhs_xpure_orig in 
      let split_rhs = CP.split_conjunctions rhs_xpure in
      let rem_rhs = List.filter (fun c -> not(TP.imply_raw lhs_xpure c)) split_rhs in
      let rhs_xpure = CP.join_conjunctions rem_rhs in
      let _ = DD.tinfo_hprint (add_str "lhs_xpure: " (!CP.print_formula)) lhs_xpure pos in
      let _ = DD.tinfo_hprint (add_str "split_rhs: " (pr_list !CP.print_formula)) split_rhs pos in
      let _ = DD.tinfo_hprint (add_str "rem_rhs: " (pr_list !CP.print_formula)) rem_rhs pos in
      let _ = DD.trace_hprint (add_str "lhs(orig): " !CP.print_formula) lhs_xpure_orig pos in
      let _ = DD.trace_hprint (add_str "lhs0(orig): " !print_mix_formula) lhs_xpure0 pos in
      let _ = DD.trace_hprint (add_str "rhs(orig): " !CP.print_formula) rhs_xpure pos in
      let lhs_xpure = CP.filter_ante lhs_xpure_orig rhs_xpure in
      let _ = DD.trace_hprint (add_str "lhs (after filter_ante): " !CP.print_formula) lhs_xpure pos in
      let fml = CP.mkAnd lhs_xpure rhs_xpure pos in
      let fml = CP.drop_rel_formula fml in
      (*      let iv_orig = estate.es_infer_vars in*)
      (* let iv_lhs_rel = match lhs_rels with *)
      (*   | None -> [] *)
      (*   | Some f -> List.filter (fun x -> not(is_rel_var x)) (CP.fv f) in *)
      (* Debug.trace_hprint (add_str "iv_lhs_rel" !CP.print_svl) iv_lhs_rel no_pos; *)
      let _ = DD.trace_hprint (add_str "fml: " !CP.print_formula) fml pos in
      (* let check_sat,fml = detect_lhs_rhs_contra (\*lhs_xpure*\) lhs_xpure_orig rhs_xpure pos in *)
      let check_sat = TP.is_sat_raw (MCP.mix_of_pure fml) in
      if not(check_sat) then
        let _ = DD.devel_pprint "LHS-RHS contradiction" pos in
        (* let lhs_xpure0 = MCP.pure_of_mix lhs_xpure0 in *)
        let _ = DD.trace_hprint (add_str "lhs0: " !print_mix_formula) lhs_xpure0 pos in
        (* let _ = DD.trace_hprint (add_str "rhs: " !CP.print_formula) rhs_xpure pos in *)
        (* let lhs_xpure0 = CP.filter_ante lhs_xpure0 rhs_xpure in *)
        (* let _ = DD.trace_hprint (add_str "lhs0 (after filter_ante): " !CP.print_formula) lhs_xpure0 pos in *)
        let p, rel_ass = infer_lhs_contra_estate 2 estate lhs_xpure0 pos "ante contradict with conseq" in
        (p,None,rel_ass)
      else
        (*let invariants = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos) estate.es_infer_invs in*)
        (* if check_sat then *)
        (*      let new_p = simplify fml iv in                            *)
        (*      let new_p = simplify (CP.mkAnd new_p invariants pos) iv in*)
        (*      if CP.isConstTrue new_p then None                         *)
        (*      else                                                      *)
        let lhs_wo_heap = CP.drop_rel_formula (MCP.pure_of_mix lhs_wo_heap_orig) in
        let lhs_wo_ptr_eqs = CP.remove_ptr_equations lhs_wo_heap false in
        let vars_lhs = fv lhs_wo_ptr_eqs in (* var on lhs *)
        let vars_rhs = fv (CP.remove_ptr_equations rhs_xpure false) in (* var on lhs *)
        let lhs_als = MCP.ptr_equations_without_null (MCP.mix_of_pure lhs_xpure) in
        let lhs_aset = build_var_aset lhs_als in
        let total_sub_flag = List.for_all (fun r ->
            let alias = r::(CP.EMapSV.find_equiv_all r lhs_aset) in
            CP.intersect alias iv != []) vars_rhs in
        let total_sub_flag = if (CP.diff_svl iv vars_rhs == []) then false else total_sub_flag in
        Debug.trace_hprint (add_str "total_sub_flag" string_of_bool) total_sub_flag no_pos;
        let vars_rhs = List.concat (List.map (fun r -> r::(CP.EMapSV.find_equiv_all r lhs_aset)) vars_rhs) in
        let vars_overlap =  if total_sub_flag then (CP.intersect_svl vars_lhs vars_rhs) else [] in
        Debug.trace_hprint (add_str "vars overlap" !CP.print_svl) vars_overlap no_pos;
        let args = CP.fv fml in (* var on lhs *)
        let quan_var = CP.diff_svl args iv in
        let _ = DD.trace_hprint (add_str "quan_var: " !CP.print_svl) quan_var pos in
        (* vars overlap do not work - see infer/imm/t3a.slk *)
        let quan_var_new = quan_var @vars_overlap in
        let is_bag_cnt = TP.is_bag_constraint fml in
        let new_p,new_p_ass = 
          if is_bag_cnt then           
            let new_p = fml in 
            let _ = DD.trace_hprint (add_str "new_p3: " !CP.print_formula) new_p pos in 
            let new_p = simplify new_p iv in 
            let _ = DD.trace_hprint (add_str "new_p4: " !CP.print_formula) new_p pos in 
            let args = CP.fv new_p in 
            let quan_var_new = CP.diff_svl args iv in 
            (TP.simplify_raw (CP.mkExists quan_var_new new_p None pos), mkFalse no_pos)
          else
            let lhs_xpure = CP.drop_rel_formula lhs_xpure in
            let _ = DD.trace_hprint (add_str "lhs_xpure: " !CP.print_formula) lhs_xpure pos  in
            let vrs1 = CP.fv lhs_xpure in
            let vrs2 = CP.fv rhs_xpure in
            let vrs = CP.remove_dups_svl (vrs1@vrs2) in
            let imm_vrs = List.filter (fun x -> (CP.type_of_spec_var x) == AnnT) (vrs) in 
            let lhs_xpure_ann = Cpure.add_ann_constraints imm_vrs lhs_xpure in
            let _ = DD.trace_hprint (add_str "lhs_xpure(w ann): " !CP.print_formula) lhs_xpure_ann pos  in
            let new_p = TP.simplify_raw (CP.mkForall quan_var_new 
                (CP.mkOr (CP.mkNot_s lhs_xpure_ann) rhs_xpure None pos) None pos) in
            let new_p = if not(isConstFalse new_p) then new_p else
              (* Use quan_var instead *)
              TP.simplify_raw (CP.mkForall quan_var 
                  (CP.mkOr (CP.mkNot_s lhs_xpure_ann) rhs_xpure None pos) None pos) in
            (*          let fml2 = TP.simplify_raw (CP.mkExists quan_var_new fml None no_pos) in*)
            let new_p_for_assume = new_p in
            (*          let new_p2 = TP.simplify_raw (CP.mkAnd new_p fml2 no_pos) in*)
            let _ = DD.trace_hprint (add_str "rhs_xpure: " !CP.print_formula) rhs_xpure pos  in
            (*          let _ = DD.trace_hprint (add_str "fml2: " !CP.print_formula) fml2 pos in*)
            (*          let _ = DD.trace_hprint (add_str "new_p2: " !CP.print_formula) new_p2 pos in*)
            let _ = DD.devel_hprint (add_str "quan_var: " !CP.print_svl) quan_var pos in
            let _ = DD.devel_hprint (add_str "quan_var_new: " !CP.print_svl) quan_var_new pos in
            let _ = DD.trace_hprint (add_str "iv: " !CP.print_svl) iv pos in
            let _ = DD.trace_hprint (add_str "new_p1: " !CP.print_formula) new_p pos in
            (* TODO Thai : Should fml be lhs_pure only *)
            let new_p = TP.simplify_raw (simplify_disjs new_p fml) in
            let _ = DD.trace_hprint (add_str "new_p: " !CP.print_formula) new_p pos in
            (* TODO : simplify_raw seems to undo pairwisecheck *)
            let new_p = TP.pairwisecheck_raw new_p in
            let _ = DD.trace_hprint (add_str "new_p (pairwisecheck): " !CP.print_formula) new_p pos in
            (new_p,new_p_for_assume)
        in
        (* TODO WN : Is below really needed?? *)
        (*      let args = CP.fv new_p in*)
        let new_p =
          (* if CP.intersect args iv == [] && quan_var != [] then *)
          (*   let new_p = if CP.isConstFalse new_p then fml else CP.mkAnd fml new_p pos in *)
          (*   let _ = DD.trace_hprint (add_str "new_p3: " !CP.print_formula) new_p pos in *)
          (*   let new_p = simplify new_p iv in *)
          (*   let _ = DD.trace_hprint (add_str "new_p4: " !CP.print_formula) new_p pos in *)
          (*   (\*let new_p = simplify (CP.mkAnd new_p invariants pos) iv in*\) *)
          (*   let args = CP.fv new_p in *)
          (*   let quan_var = CP.diff_svl args iv in *)
          (*   TP.simplify_raw (CP.mkExists quan_var new_p None pos) *)
          (* else *)
          simplify new_p iv
        in
        let _ = DD.tinfo_hprint (add_str "new_p: " !CP.print_formula) new_p pos in
        let _ = DD.tinfo_hprint (add_str "new_p_ass: " !CP.print_formula) new_p_ass pos in
        (* abstract common terms from disj into conjunctive form *)
        if (CP.isConstTrue new_p || CP.isConstFalse new_p) then 
          begin
            (* Do not add new_p_ass when new_p_ass is false or contains relation *)
            let new_p_ass_conjs = CP.list_of_conjs new_p_ass in
            let rhs_contain_rel = List.exists CP.is_RelForm new_p_ass_conjs in
            if ((lhs_rels==None && unk_heaps==[]) || not(CP.isConstFalse new_p_ass || rhs_contain_rel)) then
              begin
                DD.devel_pprint ">>>>>> infer_pure_m <<<<<<" pos;
                DD.devel_pprint "Did not manage to infer a useful precondition" pos;
                DD.devel_hprint (add_str "LHS : " !CP.print_formula) lhs_xpure pos;               
                DD.devel_hprint (add_str "RHS : " !CP.print_formula) rhs_xpure pos;
                DD.devel_hprint (add_str "LHS REL : " (pr_opt !CP.print_formula)) lhs_rels pos;
                (* DD.devel_hprint (add_str "new pure: " !CP.print_formula) new_p pos; *)
                DD.devel_hprint (add_str "new_p_ass: " !CP.print_formula) new_p_ass pos;
                DD.devel_hprint (add_str "new pure: " !CP.print_formula) new_p pos;
                (None,None,[])
              end
            else 
              match lhs_rels with
                | None ->
                      if unk_heaps==[] 
                      then (None,None,[])
                      else 
                        begin
                          DD.ninfo_pprint ">>>>>> infer_pure_m <<<<<<" pos;
                          DD.ninfo_pprint "Adding heap assumption?" pos;
                          DD.ninfo_hprint (add_str "unk_heaps" (pr_list !CF.print_h_formula)) unk_heaps pos;
                          DD.ninfo_hprint (add_str "lhs_xpure" (!CP.print_formula)) lhs_xpure pos;
                          DD.ninfo_hprint (add_str "rhs_xpure" (!CP.print_formula)) rhs_xpure pos;
                          let vs = CP.fv rhs_xpure in
                          let choose_unk_h = List.filter (fun h -> (Gen.BList.difference_eq CP.eq_spec_var vs (CF.h_fv h)) == []) unk_heaps in
                          DD.info_hprint (add_str "choose_unk_h" (pr_list !CF.print_h_formula)) choose_unk_h pos;
                          if choose_unk_h==[] then (None,None,[])
                          else 
                            (*Loc : need to add (choose_unk_h --> rhs_xpure) heap assumption*)
                            let hp_rel = {
                                CF.hprel_kind = CP.RelAssume vs;
                                unk_svl = [];
                                unk_hps = [];
                                predef_svl = [];
                                hprel_lhs = CF.formula_of_heap (List.fold_left (fun h1 h2 -> CF.mkStarH h1 h2 pos) (List.hd choose_unk_h) (List.tl choose_unk_h)) pos;
                                hprel_rhs = CF.formula_of_pure_formula rhs_xpure pos;
                            }
                            in
                            let _ = rel_ass_stk # push_list ([hp_rel]) in
                            let new_es = {estate with CF.es_infer_hp_rel = estate.CF.es_infer_hp_rel @ [hp_rel];} in
                            (Some (new_es, CP.mkTrue pos),None,[])
                        end
                | Some f ->
                      DD.devel_pprint ">>>>>> infer_pure_m <<<<<<" pos;
                      DD.devel_pprint "Add relational assumption" pos;
                      let (vs_rel,vs_lhs) = List.partition CP.is_rel_var (CP.fv f) in
                      (* TODO : how to handle multiple rel on LHS *)
                      (*              if (List.length vs_rel)>1 then *)
                      (*                let vars = stk_vars # get_stk in*)
                      (*	              let (_,n_lhs,n_rhs) = simp_lhs_rhs vars (0,lhs_xpure,rhs_xpure) in*)
                      (*(*                let lhs_xpure = CP.drop_rel_formula lhs_xpure in*)*)
                      (*                let new_estate = {estate with es_formula = *)
                      (*                    (match estate.es_formula with*)
                      (*                    | Base b -> CF.mkBase_simp b.formula_base_heap *)
                      (*                      (MCP.mix_of_pure (TP.simplify_raw (CP.mkAnd lhs_xpure n_rhs pos)))*)
                      (*                    | _ -> report_error pos "infer_pure_m: Not supported")*)
                      (*                  } *)
                      (*                in*)
                      (*                let rel_ass = [RelAssume vs_rel,n_lhs,n_rhs] in*)
                      (*                let _ = infer_rel_stk # push_list rel_ass in*)
                      (*                let _ = Log.current_infer_rel_stk # push_list rel_ass in*)
                      (*                (None,None,[(new_estate,rel_ass)])*)
                      (*              else*)
                      let rhs_xpure_orig,rels = 
                        if not rhs_contain_rel then rhs_xpure_orig,[]
                        else
                          let rels,others = List.partition CP.is_RelForm (CP.list_of_conjs rhs_xpure) in
                          MCP.mix_of_pure (CP.conj_of_list others pos), rels
                      in
                      let (ip1,ip2,rs) = infer_pure_m unk_heaps estate None (CP.drop_rel_formula lhs_xpure_orig) lhs_xpure0 
                        lhs_wo_heap_orig rhs_xpure_orig vs_lhs pos in
                      let rels = List.filter (fun r -> CP.subset (CP.fv_wo_rel_r r) vs_lhs) rels in
                      let p_ass = (match ip2 with
                        | None -> ([],rels)
                        | Some a -> if (CP.fv a == []) then ([],rels) else (CP.list_of_conjs a), rels)
                      in
                      let _ = DD.devel_hprint (add_str "rel_ass : " (pr_pair (pr_list !CP.print_formula) 
                          (pr_list !CP.print_formula))) p_ass pos in
                      begin
                        match p_ass with
                          | [],[] -> (None,None,[])
                          | (ps,rs) ->
                                let rel_ass = 
                                  if List.length (List.concat (List.map CP.get_rel_id_list (CP.list_of_conjs f)))=1 then
                                    [RelAssume vs_rel,f,CP.conj_of_list (ps@rs) pos]
                                  else
                                    let p_ass_conjs = if ps = [] then [] else
                                      let lhs_xpure_new = CP.drop_rel_formula lhs_xpure in
                                      let tmp = CP.conj_of_list ps pos in
                                      let tmp = Omega.gist tmp lhs_xpure_new in 
                                      if CP.subset (CP.fv tmp) vs_lhs then CP.list_of_conjs tmp else ps
                                        (*                          let lhs_xpure_new = CP.drop_rel_formula lhs_xpure in*)
                                        (*                          let lhs_xpure_conjs = List.filter (fun x -> match x with*)
                                        (*                            | BForm ((Eq _,_),_) -> true | _ -> false) (CP.list_of_conjs lhs_xpure_new) in*)
                                        (*                          let lhs_xpure_new2 = CP.conj_of_list lhs_xpure_conjs pos in*)
                                        (*                          let p = TP.simplify_raw (CP.mkAnd (CP.conj_of_list ps pos) lhs_xpure_new2 pos) in*)
                                        (*                          List.filter (fun x -> not(TP.imply_raw lhs_xpure_new x)) (CP.list_of_conjs p) *)
                                    in
                                    (* TODO: Need better split RHS *)
                                    List.concat (List.map (fun x -> 
                                        let lhs_conjs = List.filter (fun y -> 
                                            CP.intersect (CP.fv y) (CP.fv x) != []) (CP.list_of_conjs f) in
                                        let rel_ids = List.concat (List.map get_rel_id_list lhs_conjs) in
                                        if CP.remove_dups_svl rel_ids = rel_ids && lhs_conjs != [] then
                                          [RelAssume vs_rel,CP.conj_of_list lhs_conjs pos,x]
                                        else []
                                    ) (p_ass_conjs @ rs))
                                in
                                if rel_ass = [] then (None,None,[])
                                else
                                  let new_estate = {estate with es_formula = 
                                          (match estate.es_formula with
                                            | Base b -> CF.mkBase_simp b.formula_base_heap 
                                                  (MCP.mix_of_pure (TP.simplify_raw (CP.mkAnd lhs_xpure (CP.conj_of_list (ps@rs) pos) pos)))
                                            | _ -> report_error pos "infer_pure_m: Not supported")
                                  } 
                                  in
                                  let _ = DD.ninfo_hprint (add_str "LHS : " !CP.print_formula) lhs_xpure pos in           
                                  let _ = DD.devel_hprint (add_str "rel_ass_final: " (pr_list print_lhs_rhs)) rel_ass pos in
                                  let _ = DD.devel_hprint (add_str "New estate : " !print_entail_state_short) new_estate pos in
                                  let _ = infer_rel_stk # push_list rel_ass in
                                  let _ = Log.current_infer_rel_stk # push_list rel_ass in
                                  (None,None,[(new_estate,rel_ass,false)])
                      end
                          (*                  DD.devel_pprint ">>>>>> infer_pure_m <<<<<<" pos;*)
                          (*                  DD.devel_pprint "Add relational assumption" pos;*)
                          (*                  DD.devel_hprint (add_str "new pure: " !CP.print_formula) new_p pos;*)
                          (*                  DD.devel_hprint (add_str "new pure ass: " !CP.print_formula) new_p_ass pos;*)
                          (*                  let (vs_rel,vs_lhs) = List.partition CP.is_rel_var (CP.fv f) in*)
                          (*                  let n_rhs = rhs_xpure in*)
                          (*                  let n_lhs = lhs_xpure in*)
                          (*                  (* let vars = stk_vars # get_stk in *)*)
                          (*			            (* let (_,n_lhs,n_rhs) = simp_lhs_rhs vars (0,lhs_xpure,rhs_xpure) in *)*)
                          (*                  (* TODO : how to handle multiple rel on LHS *)*)
                          (*                  if ((List.length vs_rel)>1) then *)
                          (*                    let vars = stk_vars # get_stk in*)
                          (*			              let (_,n_lhs,n_rhs) = simp_lhs_rhs vars (0,lhs_xpure,rhs_xpure) in*)
                          (*                    (* (None,None,[]) *)*)
                          (*                    let rel_ass = [RelAssume vs_rel,n_lhs,n_rhs] in*)
                          (*                    let _ = infer_rel_stk # push_list rel_ass in*)
                          (*                    let _ = Log.current_infer_rel_stk # push_list rel_ass in*)
                          (*                    (None,None,rel_ass)*)
                          (*                  else*)
                          (*                    begin*)
                          (*                  let n_lhs2 = CP.drop_rel_formula n_lhs in*)
                          (*(*                  let n_lhs3 = filter_ante n_lhs2 n_rhs in*)*)
                          (*                  let n_lhs3 = filter_var n_lhs2 vs_lhs in*)
                          (*                  let args = CP.remove_dups_svl (CP.fv n_lhs3 @ CP.fv n_rhs) in*)
                          (*                  (* Update vars_overlap with vars_lhs *)*)
                          (*                  let total_sub_flag = List.for_all (fun r ->*)
                          (*                    let alias = r::(CP.EMapSV.find_equiv_all r lhs_aset) in*)
                          (*                    CP.intersect alias vs_lhs != []) vars_rhs in*)
                          (*                  let total_sub_flag = if (CP.diff_svl vs_lhs vars_rhs == []) then false else total_sub_flag in*)
                          (*                  Debug.trace_hprint (add_str "total_sub_flag" string_of_bool) total_sub_flag no_pos;*)
                          (*                  let vars_rhs = List.concat (List.map (fun r -> r::(CP.EMapSV.find_equiv_all r lhs_aset)) vars_rhs) in*)
                          (*                  let vars_overlap =  if total_sub_flag then (CP.intersect_svl vars_lhs vars_rhs) else [] in*)
                          (*                  Debug.info_hprint (add_str "vars overlap" !CP.print_svl) vars_overlap no_pos;*)
                          (*                  let quan_var = (CP.diff_svl args vs_lhs) @ vars_overlap in*)
                          (*                  Debug.info_hprint (add_str "quan vars" !CP.print_svl) quan_var no_pos;*)
                          (*                  let new_p = TP.simplify_raw (CP.mkForall quan_var *)
                          (*                      (CP.mkOr (CP.mkNot_s n_lhs3) n_rhs None pos) None pos) in*)
                          (*                 let _ = DD.info_hprint (add_str "rel_ass: " !CP.print_formula) new_p pos in*)
                          (*                 let trace = Debug.tinfo_hprint in*)
                          (*                  trace (add_str "f (rel)" !print_formula) f no_pos;*)
                          (*                  trace (add_str "vs_rel" !print_svl) vs_rel no_pos;*)
                          (*                  trace (add_str "vs_lhs" !print_svl) vs_lhs no_pos;*)
                          (*                  trace (add_str "quan" !print_svl) quan_var no_pos;*)
                          (*                  trace (add_str "lhs (after drop_compl)" !print_formula) n_lhs2 no_pos;*)
                          (*                  trace (add_str "lhs (after filter)" !print_formula) n_lhs3 no_pos;*)
                          (*                  trace (add_str "rhs" !print_formula) n_rhs no_pos;*)
                          (*                  trace (add_str "new_p (rel_ass)" !print_formula) new_p no_pos;*)
                          (*                  if (CP.fv new_p == []) then (None,None,[])*)
                          (*                  else *)
                          (*                    let rel_ass = [RelAssume vs_rel,f,new_p] in*)
                          (*                    let _ = infer_rel_stk # push_list rel_ass in*)
                          (*                    let _ = Log.current_infer_rel_stk # push_list rel_ass in*)
                          (*                    (None,None,rel_ass)*)
                          (*                  end*)
                (* | None -> (None,None,[]) *)
          end
        else
          let new_p_good = CP.simplify_disj_new new_p in
          (* remove ctr already present in the orig LHS *)
          let lhs_orig_list = CP.split_conjunctions lhs_xpure in
          let pre_list = CP.split_conjunctions new_p_good in
          let (red_pre,pre_list) = List.partition (present_in lhs_orig_list) pre_list in
          if pre_list==[] then (
              DD.devel_pprint ">>>>>> infer_pure_m <<<<<<" pos;
              DD.devel_pprint "Inferred pure is already in lhs" pos;
              (None,None,[]))
          else 
            let new_p_good = CP.join_conjunctions pre_list in
            (*let pre_thus = estate.es_infer_pure_thus in
              let b = if CP.isConstTrue pre_thus then false
              else let f = CP.mkAnd pre_thus new_p_good no_pos in
              not(TP.is_sat_raw f) 
              in*)
            (* filter away irrelevant constraint for infer_pure *)
            (* let new_p_good = CP.filter_ante new_p rhs_xpure in *)
            (* let _ = print_endline ("new_p:"^(!CP.print_formula new_p)) in *)
            (* let _ = print_endline ("new_p_good:"^(!CP.print_formula new_p_good)) in *)
            (* should not be using es_orig_ante *)
            (* let _,ante_pure,_,_,_ = CF.split_components estate.es_orig_ante in *)
            (* let ante_conjs = CP.list_of_conjs (MCP.pure_of_mix ante_pure) in *)
            (* let new_p_conjs = CP.list_of_conjs new_p_good in *)
            (* below redundant with filter_ante *)
            (* let new_p = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos) *)
            (*    (List.filter (fun c -> not (is_elem_of c ante_conjs)) new_p_conjs) in *)
            (* if CP.isConstTrue new_p || CP.isConstFalse new_p then (None,None) *)
            (* else *)
            begin
              (* TODO WN : Is rel assume still needed here?? *)
              (* let lhs_fil = CP.filter_ante lhs_xpure rhs_xpure in *)
              (* let lhs_simps = CP.simplify_filter_ante TP.simplify_always lhs_xpure rhs_xpure in *)
              (* DD.devel_pprint ">>>>>> infer_pure_m <<<<<<" pos; *)
              (* DD.devel_pprint ">>>>>> rel assume <<<<<<" pos; *)
              (* DD.devel_hprint (add_str "LHS" !CP.print_formula) lhs_xpure pos;                *)
              (* DD.devel_hprint (add_str "LHS filter" !CP.print_formula) lhs_fil pos;                *)
              (* DD.devel_hprint (add_str "LHS simpl" !CP.print_formula) lhs_simps pos;                *)
              (* DD.devel_hprint (add_str "RHS" !CP.print_formula) rhs_xpure pos; *)
              (* DD.devel_hprint (add_str "lhs_rels" (pr_opt !CP.print_formula)) lhs_rels pos; *)
              (* DD.devel_hprint (add_str "iv_orig" (!CP.print_svl)) iv_orig pos; *)
              (* (\* DD.devel_hprint (add_str "new pure: " !CP.print_formula) new_p pos; *\) *)
              (* if red_pre!=[] then DD.devel_hprint (add_str "already in LHS: " (pr_list !CP.print_formula)) red_pre pos; *)
              (* DD.devel_hprint (add_str "new pure: " !CP.print_formula) new_p_good pos; *)
              (* DD.devel_hprint (add_str "contradict?: " string_of_bool) b pos; *)
              (* if b then *)
              (*   (DD.devel_pprint "contradiction in inferred pre!" pos; (None,None)) *)
              (* else *)
              (None,Some new_p_good,[])
                  (* let ans,rel_ass =  *)
                  (*   let ans =Some new_p_good in *)
                  (*   match lhs_rels with *)
                  (*     | None -> ans,[] *)
                  (*     | Some f -> *)
                  (*          if (CP.diff_svl (CP.fv new_p_good) iv_orig)==[] then ans,[]  *)
                  (*           else  *)
                  (*             let vars = stk_vars # get_stk in *)
                  (*             let vs = List.filter CP.is_rel_var (CP.fv f) in *)
		  (*             let (_,n_lhs,n_rhs) = simp_lhs_rhs vars (0,lhs_xpure,rhs_xpure) in *)
                  (*             Debug.tinfo_hprint (add_str "lhs (after filter)" !print_formula) n_lhs no_pos;                         *)
                  (*             (\* ans,[(RelAssume vs,f,new_p_good)] *\) *)
                  (*             None,[(RelAssume vs,n_lhs,n_rhs)] *)
                  (* in (None,ans,rel_ass) *)
            end
                (* Thai: Should check if the precondition overlaps with the orig ante *)
                (* And simplify the pure in the residue *)
                (*           let new_es_formula = normalize 0 estate.es_formula (CF.formula_of_pure_formula new_p pos) pos in *)
                (* (\*          let h, p, fl, b, t = CF.split_components new_es_formula in                                                 *\) *)
                (* (\*          let new_es_formula = Cformula.mkBase h (MCP.mix_of_pure (Omega.simplify (MCP.pure_of_mix p))) t fl b pos in*\) *)
                (*           let args = List.filter (fun v -> if is_substr "inf" (name_of_spec_var v) then true else false) (CP.fv new_p) in *)
                (*           let new_iv = CP.diff_svl iv args in *)
                (*           let new_estate = *)
                (*             {estate with  *)
                (*                 es_formula = new_es_formula; *)
                (*                 (\* es_infer_pure = estate.es_infer_pure@[new_p]; *\) *)
                (*                 es_infer_vars = new_iv *)
                (*             } *)
                (*           in *)
                (* below removed because of ex/bug-3e.slk *)
                (* else *)
                (*   (\* contradiction detected *\) *)
                (*   (infer_lhs_contra_estate estate lhs_xpure_orig pos "ante contradict with conseq",None) *)
                (*       let check_sat = TP.is_sat_raw lhs_xpure in *)
                (*       if not(check_sat) then None *)
                (*       else *)
                (*         let lhs_simplified = simplify lhs_xpure iv in *)
                (*         let args = CP.fv lhs_simplified in *)
                (*         let exists_var = CP.diff_svl args iv in *)
                (*         let lhs_simplified = simplify_helper (CP.mkExists exists_var lhs_simplified None pos) in *)
                (*         (\*let new_p = simplify_contra (CP.mkAnd (CP.mkNot_s lhs_simplified) invariants pos) iv in*\) *)
                (*         let new_p = simplify_contra (CP.mkNot_s lhs_simplified) iv in *)
                (*         if CP.isConstFalse new_p || CP.isConstTrue new_p then None *)
                (*         else *)
                (* (\*          let args = CP.fv new_p in *\) *)
                (*           (\* let new_iv = (CP.diff_svl iv args) in *\) *)
                (*           let new_estate = *)
                (*             {estate with *)
                (*                 es_formula = CF.mkFalse (CF.mkNormalFlow ()) pos *)
                (*                 (\* ;es_infer_pure = estate.es_infer_pure@[new_p] *\) *)
                (*                     (\* ;es_infer_vars = new_iv *\) *)
                (*             } *)
                (*           in *)
                (*           Some (new_estate,new_p) *)
                (*
                  Cformula.entail_state ->
                  MCP.mix_formula (LHS) ->
                  MCP.mix_formula (RHS) ->
                  Globals.loc -> (Cformula.entail_state * CP.formula) option
                *)

(*
  (CF.entail_state * Cformula.CP.formula) option *
  CP.Label_Pure.exp_ty option *

  (CF.entail_state *
  (Cpure.rel_cat * Cpure.Label_Pure.exp_ty * Redlog.CP.formula) list * 
  bool)
  list
*)
and infer_pure_m unk_heaps estate lhs_rels lhs_xpure_orig lhs_xpure0 lhs_wo_heap_orig rhs_xpure_orig iv_orig pos =
  let pr1 = !print_mix_formula in 
  let pr2 = !print_entail_state_short in 
  let pr_p = !CP.print_formula in
  let pr_res_lst = pr_list (fun (es,r,b) -> (pr_pair (pr2) (pr_list CP.print_lhs_rhs)) (es,r)) in
  let pr_res = pr_triple (pr_option (pr_pair pr2 !print_pure_f)) (pr_option pr_p) pr_res_lst in
  let pr0 es = pr_pair pr2 !CP.print_svl (es,es.es_infer_vars) in
  Debug.no_5 "infer_pure_m_1" 
      (add_str "estate " pr0) 
      (add_str "lhs xpure " pr_p) 
      (add_str "lhs xpure0 " pr1)
      (add_str "rhs xpure " pr1)
      (add_str "inf vars " !CP.print_svl)
      (add_str "(new es,inf pure,rel_ass) " pr_res)
      (fun _ _ _ _ _ -> infer_pure_m_x unk_heaps estate lhs_rels lhs_xpure_orig lhs_xpure0 lhs_wo_heap_orig rhs_xpure_orig iv_orig pos) 
      estate lhs_xpure_orig lhs_xpure0 rhs_xpure_orig iv_orig

let infer_pure_m unk_heaps estate lhs_mix lhs_mix_0 lhs_wo_heap rhs_mix pos =
  if no_infer_all estate && unk_heaps==[] then 
    (None,None,[])
  else 
    let ivs = estate.es_infer_vars_rel@estate.es_infer_vars_hp_rel in
    (* let rhs_p = MCP.pure_of_mix rhs_mix in *)
    let lhs_p = MCP.pure_of_mix lhs_mix in
    (* TODO: For relational obligation *)
(*    let cl = CP.filter_ante lhs_p rhs_p in*)
    (* Assumed cl is a conjunction *)
    let cl = CP.split_conjunctions lhs_p in
    let (lhs_rel, lhs_wo_rel) = 
      List.partition (fun d -> (CP.get_RelForm d) != [] ) cl in
    (* TODO: Double check *)
    (* Debug.info_hprint (add_str "lhs_rel" (pr_list !CP.print_formula)) lhs_rel no_pos; *)
    (* Debug.info_hprint (add_str "lhs_rel" (pr_list !CP.print_formula)) lhs_wo_rel no_pos; *)
    let lhs_rel = List.filter (fun d -> (CP.intersect (CP.fv d) ivs) != [] ) lhs_rel in
    (* Debug.info_hprint (add_str "lhs_rel" (pr_list pr_none)) lhs_rel no_pos; *)
    let lhs_rels,xp = match lhs_rel with 
      | [] -> None, join_conjunctions lhs_wo_rel
      | _ -> 
        Debug.trace_hprint (add_str "lhs_rels" (pr_list !CP.print_formula)) lhs_rel no_pos;
        let v = join_conjunctions lhs_rel in
        Some v, join_conjunctions (v::lhs_wo_rel)
    in
    Debug.tinfo_hprint (add_str "lhs_p" !CP.print_formula) lhs_p no_pos;
    Debug.tinfo_hprint (add_str "lhs_mix_0" !print_mix_formula) lhs_mix_0 no_pos;
    Debug.tinfo_hprint (add_str "lhs_rels" (pr_opt !CP.print_formula)) lhs_rels no_pos;
    Debug.tinfo_hprint (add_str "xp" !CP.print_formula) xp no_pos;
    Debug.ninfo_hprint (add_str "infer_vars_rel" !CP.print_svl) estate.es_infer_vars_rel no_pos;
    Debug.ninfo_hprint (add_str "infer_vars_hp_rel" !CP.print_svl) estate.es_infer_vars_hp_rel  no_pos;
    let infer_vars = estate.es_infer_vars@estate.es_infer_vars_hp_rel in 
    infer_pure_m unk_heaps estate lhs_rels xp lhs_mix_0 lhs_wo_heap rhs_mix infer_vars pos

let infer_pure_m i unk_heaps estate lhs_xpure lhs_xpure0 lhs_wo_heap rhs_xpure pos =
  let pr1 = !print_mix_formula in 
  let pr2 = !print_entail_state_short in 
  (* let pr2a = !print_entail_state in  *)
  let pr_p = !CP.print_formula in
  let pr_res_lst = pr_list (fun (es,r,b) -> pr_pair pr2 (pr_list CP.print_lhs_rhs) (es,r)) in
  (* let pr_len = fun l -> (string_of_int (List.length l)) in *)
  let pr_res = pr_triple (pr_option (pr_pair pr2 !print_pure_f)) (pr_option pr_p) pr_res_lst in
  let pr0 es = pr_pair pr2 !CP.print_svl (es,es.es_infer_vars) in
  Debug.ho_4_num i "infer_pure_m_2" 
    (add_str "estate " pr0) 
    (add_str "lhs xpure " pr1) 
    (add_str "lhs xpure0 " pr1)
    (add_str "rhs xpure " pr1)
    (add_str "(new es,inf pure,rel_ass) " pr_res)
  (fun _ _ _ _ -> infer_pure_m unk_heaps estate lhs_xpure lhs_xpure0 lhs_wo_heap rhs_xpure pos) 
    estate lhs_xpure lhs_xpure0 rhs_xpure   

(*let remove_contra_disjs f1s f2 =*)
(*  let helper c1 c2 = *)
(*    let conjs1 = CP.list_of_conjs c1 in*)
(*    let conjs2 = CP.list_of_conjs c2 in*)
(*    (Gen.BList.intersect_eq CP.equalFormula conjs1 conjs2) != []*)
(*  in *)
(*  let new_f1s = List.filter (fun f -> helper f f2) f1s in*)
(*  match new_f1s with*)
(*    | [] -> f1s*)
(*    | [hd] -> [hd]*)
(*    | ls -> f1s*)
  

(*let lhs_simplifier lhs_h lhs_p =*)
(*  let disjs = CP.list_of_disjs lhs_h in*)
(*  let disjs = remove_contra_disjs disjs lhs_p in*)
(*  snd (trans_dnf (CP.mkAnd (disj_of_list disjs no_pos) lhs_p no_pos))*)

(* TODO : proc below seems very inefficient *)
(*let rec simplify_fml pf =                                         *)
(*  let helper fml =                                                *)
(*    let fml = CP.drop_rel_formula fml in                          *)
(*    if TP.is_sat_raw fml then remove_dup_constraints fml          *)
(*    else CP.mkFalse no_pos                                        *)
(*  in                                                              *)
(*  match pf with                                                   *)
(*  | BForm _ -> if CP.isConstFalse pf then pf else helper pf       *)
(*  | And _ -> helper pf                                            *)
(*  | Or (f1,f2,l,p) -> mkOr (simplify_fml f1) (simplify_fml f2) l p*)
(*  | Forall (s,f,l,p) -> Forall (s,simplify_fml f,l,p)             *)
(*  | Exists (s,f,l,p) -> Exists (s,simplify_fml f,l,p)             *)
(*  | _ -> pf                                                       *)

(* a good simplifier is needed here *)
(*let lhs_simplifier lhs_h lhs_p =                                   *)
(*    let lhs = simplify_fml (trans_dnf(mkAnd lhs_h lhs_p no_pos)) in*)
(*    lhs                                                            *)

let lhs_simplifier_tp lhs_h lhs_p =
  TP.simplify_raw_w_rel (mkAnd lhs_h lhs_p no_pos)

let lhs_simplifier_tp lhs_h lhs_p =
  let pr = !CP.print_formula in
  Debug.no_2 "lhs_simplifier_tp" pr pr pr lhs_simplifier_tp lhs_h lhs_p

(* to filter relevant LHS term for selected relation rel *)
(* requires simplify and should preserve relation and != *)
let rel_filter_assumption is_sat lhs rel =
  let (lhs,rel) = CP.assumption_filter_aggressive is_sat lhs rel in
  (lhs,rel)

(* let rel_filter_assumption lhs rel = *)
(*   let pr = CP.print_formula in *)
(*   Debug.no_2 "rel_filter_assumption" pr pr (fun (r,_) -> pr r) rel_filter_assumption lhs rel  *)

(*let delete_present_in i_pure compared_pure_list =*)
(*  let i_pure_list = CP.split_conjunctions i_pure in*)
(*  let i_pure_list = List.filter (fun p -> not (present_in compared_pure_list p)) i_pure_list in*)
(*  CP.join_conjunctions i_pure_list*)

(*let check_rank_dec rank_fml lhs_cond = match rank_fml with
  | BForm (bf,_) ->
    (match bf with
    | (Gt (Func (id1,args1,_), Func (id2,args2,_),_),_) ->
      if id1 = id2 && List.length args1 = List.length args2 then
        let fml = CP.disj_of_list (List.map2 (fun e1 e2 -> CP.mkNeqExp e1 e2 no_pos) args1 args2) no_pos in
        if not(TP.is_sat_raw (CP.mkAnd lhs_cond fml no_pos)) then CP.mkFalse no_pos else rank_fml
      else rank_fml
    | (Lt (Func (id1,args1,_), Func (id2,args2,_),_),_) -> 
      if id1 = id2 && List.length args1 = List.length args2 then
        let fml = CP.disj_of_list (List.map2 (fun e1 e2 -> CP.mkNeqExp e1 e2 no_pos) args1 args2) no_pos in
        if not(TP.is_sat_raw (CP.mkAnd lhs_cond fml no_pos)) then CP.mkFalse no_pos else rank_fml
      else rank_fml
    | _ -> rank_fml)    
  | _ -> rank_fml
    
let check_rank_const rank_fml lhs_cond = match rank_fml with
  | BForm (bf,_) ->
    (match bf with
    | (Eq (Func (id1,args1,_), Func (id2,args2,_),_),_) ->
      if id1 = id2 && List.length args1 = List.length args2 then
        let fml = CP.join_conjunctions (List.map2 (fun e1 e2 -> CP.mkEqExp e1 e2 no_pos) args1 args2) in
        if not(TP.is_sat_raw (CP.mkAnd lhs_cond fml no_pos)) then CP.mkFalse no_pos else CP.mkTrue no_pos
      else CP.mkTrue no_pos
    | _ -> CP.mkTrue no_pos)
  | _ -> CP.mkTrue no_pos*)

(* let find_close_infer_vars_rel_x lhs_mix es_infer_vars_rel= *)
(*   let eqs = MCP.ptr_equations_without_null lhs_mix in *)
(*   let eqs_rels = List.filter (fun (sv1,_) -> CP.is_rel_typ sv1) eqs in *)
(*   let new_infer_vars_rel = SAU.find_close es_infer_vars_rel eqs_rels in *)
(*   (CP.remove_dups_svl new_infer_vars_rel) *)

(* let find_close_infer_vars_rel lhs_mix es_infer_vars_rel= *)
(*   let pr1= !CP.print_svl in *)
(*   let pr2 = Cprinter.string_of_mix_formula in *)
(*   Debug.no_2 "find_close_infer_vars_rel" pr2 pr1 pr1 *)
(*       (fun _ _ -> find_close_infer_vars_rel_x lhs_mix es_infer_vars_rel) lhs_mix es_infer_vars_rel *)

(* Assume fml is conjs *)
(*let filter_rank fml lhs_cond =
  let (rank, others) = List.partition (fun p -> CP.is_Rank_Dec p || CP.is_Rank_Const p) (CP.split_conjunctions fml) in
  let (rank_dec, rank_const) = List.partition (fun p -> CP.is_Rank_Dec p) rank in
  let rank_dec = List.map (fun r -> check_rank_dec r lhs_cond) rank_dec in
  let rank_const = List.map (fun r -> check_rank_const r lhs_cond) rank_const in
  CP.join_conjunctions (rank_dec@rank_const@others) *)

let detect_lhs_rhs_contra2 ivs lhs_c rhs_mix pos =
  let rhs_p = MCP.pure_of_mix rhs_mix in
  let pairs = List.map
    (fun pure -> let rhs_ls = CP.split_conjunctions pure in
      let rels, others = List.partition
        (fun p -> CP.is_rel_in_vars ivs p(* || CP.has_func p*)) rhs_ls in
      (rels, others))
    (CP.list_of_disjs rhs_p)
  in
  let rel_rhs_ls, other_rhs_ls = List.split pairs in
  (* let rel_rhs = List.concat rel_rhs_ls in *)
  (* let other_rhs = List.concat other_rhs_ls in *)
  (* let pr = Cprinter.string_of_pure_formula_list in *)
  (* DD.tinfo_hprint (add_str "rel_rhs" pr) rel_rhs pos;  *)
  (* DD.tinfo_hprint (add_str "other_rhs" pr) other_rhs pos;  *)
  let rhs_p_new = CP.disj_of_list 
    ((List.map (fun x -> CP.join_conjunctions x)
        other_rhs_ls)(*@other_disjs*)) no_pos in
  (* let lhs_p = MCP.pure_of_mix lhs_mix in *)
  (* let lhs_h_p = MCP.pure_of_mix lhs_h_mix in *)
  (* let lhs_c = CP.mkAnd lhs_p lhs_h_p pos in *)
  let fml = CP.mkAnd lhs_c rhs_p_new pos in
  let fml = CP.drop_rel_formula fml in
  let check_sat = TP.is_sat_raw (MCP.mix_of_pure fml) in
  check_sat,rhs_p_new

(*type: CP.spec_var list ->
  CP.Label_Pure.exp_ty ->
  MCP.mix_formula -> Globals.loc -> bool * CP.Label_Pure.exp_ty
               *)

let detect_lhs_rhs_contra2 ivs lhs_c rhs_mix pos =
     let pr1 = Cprinter.string_of_spec_var_list in
     let pr2 = Cprinter.string_of_pure_formula in
     let pr3 = Cprinter.string_of_mix_formula in
     let pr = pr_pair string_of_bool pr2 in
     Debug.no_3 "detect_lhs_rhs_contra2" (add_str "ivs" pr1) 
     (add_str "lhs" pr2) 
     (add_str "rhs" pr3) 
     (add_str "(res,new_rhs)" pr)
     (fun _ _ _ -> detect_lhs_rhs_contra2 ivs lhs_c rhs_mix pos) ivs lhs_c rhs_mix 

let infer_collect_rel is_sat estate lhs_h_mix lhs_mix rhs_mix pos =
  (* TODO : need to handle pure_branches in future ? *)
  if no_infer_rel estate (* && no_infer_hp_rel estate *) then (estate,lhs_mix,rhs_mix,None,[]) 
  else 
    let ivs = estate.es_infer_vars_rel(* @estate.es_infer_vars_hp_rel *)  in
    Debug.info_hprint (add_str "ivs" Cprinter.string_of_spec_var_list) ivs no_pos;
    (*add instance of relational s0-pred*)
    (* let new_es_infer_vars_rel = find_close_infer_vars_rel lhs_mix estate.CF.es_infer_vars_rel in *)
    (* let estate = { estate with CF.es_infer_vars_rel = new_es_infer_vars_rel} in *)
    let rhs_p = MCP.pure_of_mix rhs_mix in
    (*    (* Eliminate dijs in rhs which cannot be implied by lhs and do not contain relations *)*)
    (*    (* Suppose rhs_p is in DNF *)*)
    (*    (* Need to assure that later *)*)
    (*    let rhs_disjs = CP.list_of_disjs rhs_p in*)
    (*    let (rhs_disjs_rel, rhs_disjs_wo_rel) = *)
    (*      List.partition (fun d -> CP.get_RelForm d != [] || CP.get_Rank d != []) rhs_disjs in*)
    (*    let lhs_cond = MCP.pure_of_mix lhs_mix in*)
    (*    let rhs_disjs_wo_rel_new, other_disjs = List.partition (fun d -> TP.imply_raw lhs_cond d) rhs_disjs_wo_rel in*)
    (*    let other_disjs = List.filter (fun d -> TP.is_sat_raw (CP.mkAnd lhs_cond d no_pos)) other_disjs in*)
    (*    (* DD.devel_hprint (add_str "LHS pure" !CP.print_formula) (MCP.pure_of_mix lhs_mix) pos; *)*)
    (*    (* DD.devel_hprint (add_str "RHS Disj List" (pr_list !CP.print_formula)) rhs_disjs pos; *)*)
    (*    let pairs = List.map (fun pure ->*)
    (*      let rhs_ls = CP.split_conjunctions pure in*)
    (*      let rels, others = List.partition (fun p -> CP.is_rel_in_vars ivs p || CP.has_func p) rhs_ls in*)
    (*      let rels = if List.exists (fun p -> CP.is_Rank_Const p) rels then [CP.conj_of_list rels no_pos] else rels in*)
    (*      rels, others)*)
    (*      (rhs_disjs_rel @ rhs_disjs_wo_rel_new) in*)

    (* rhs_p is in DNF *)
    let pairs = List.map 
      (fun pure -> let rhs_ls = CP.split_conjunctions pure in
      let rels, others = List.partition 
        (fun p -> CP.is_rel_in_vars ivs p(* || CP.has_func p*)) rhs_ls in 
      (rels, others)) 
      (CP.list_of_disjs rhs_p) 
    in
    let rel_rhs_ls, other_rhs_ls = List.split pairs in
    let rel_rhs = List.concat rel_rhs_ls in
    let other_rhs = List.concat other_rhs_ls in
    let pr = Cprinter.string_of_pure_formula_list in
    DD.tinfo_hprint (add_str "rel_rhs" pr) rel_rhs pos; 
     DD.tinfo_hprint (add_str "other_rhs" pr) other_rhs pos; 
    if rel_rhs==[] then (
        DD.tinfo_pprint ">>>>>> infer_collect_rel <<<<<<" pos; 
        DD.tinfo_pprint "no relation in rhs" pos; 
        (estate,lhs_mix,rhs_mix,None,[])
    )
    else 
      (* let rhs_p_new = CP.disj_of_list  *)
      (*   ((List.map (fun x -> CP.join_conjunctions x) *)
      (*       other_rhs_ls)(\*@other_disjs*\)) no_pos in *)
      let lhs_p = MCP.pure_of_mix lhs_mix in
      let lhs_h_p = MCP.pure_of_mix lhs_h_mix in
      let lhs_c = CP.mkAnd lhs_p lhs_h_p pos in
      (* let fml = CP.mkAnd lhs_c rhs_p_new pos in *)
      (* let fml = CP.drop_rel_formula fml in *)
      (* let check_sat = TP.is_sat_raw (MCP.mix_of_pure fml) in *)
      let check_sat,rhs_p_new = detect_lhs_rhs_contra2 ivs lhs_c rhs_mix pos in 
      let rhs_mix_new = MCP.mix_of_pure rhs_p_new in
      if not(check_sat) then
        begin
          let p, rel_ass = infer_lhs_contra_estate 3 estate lhs_mix pos "infer_collect_rel: ante contradict with conseq" in
          DD.dinfo_pprint ">>>>>> infer_collect_rel <<<<<<" pos;
          DD.dinfo_pprint "LHS and RHS Contradiction detected for:" pos; 
          DD.dinfo_hprint (add_str "lhs" Cprinter.string_of_pure_formula) lhs_c no_pos;
          DD.dinfo_hprint (add_str "rhs" Cprinter.string_of_pure_formula) rhs_p_new no_pos;
          DD.dinfo_pprint "Skip collection of following RELDEFN:" pos; 
          DD.dinfo_hprint (add_str "rel defns" (pr_list Cprinter.string_of_pure_formula)) rel_rhs no_pos;
          (estate,lhs_mix,rhs_mix_new,p,rel_ass)
        end
      else
        let (lhs_p_memo,subs,bvars) = CP.memoise_rel_formula ivs lhs_p in
        (*let ranks = List.filter CP.has_func rel_rhs in*)

        (* Eliminate relations whose recursive calls are not defined *)
        (* e.g. A(x) <- A(t) && other_constraints, *)
        (* where other_constraints are independent from t *)
        let _,rel_lhs = List.split subs in
        let rel_lhs_n = List.concat (List.map CP.get_rel_id_list rel_lhs) in
        let rel_rhs_n = List.concat (List.map CP.get_rel_id_list rel_rhs) in
        let rel_lhs_n = CP.intersect rel_lhs_n rel_rhs_n in
        let rel_to_del = if rel_lhs_n=[] then []
        else 
          let lhs_rec_vars = CP.fv lhs_p_memo in
          let rel_lhs_new = List.filter (fun x -> CP.subset (CP.get_rel_id_list x) rel_lhs_n) rel_lhs in
          List.filter (fun x -> CP.intersect lhs_rec_vars (CP.fv x) = []) rel_lhs_new
        in
        DD.ninfo_hprint (add_str "rel_to_del:" (pr_list !CP.print_formula)) rel_to_del pos;
        (* let lhs_h_p = MCP.pure_of_mix lhs_h_mix in *)
        let lhs = lhs_simplifier_tp lhs_h_p lhs_p_memo in
        let lhs_p_new = CP.restore_memo_formula subs bvars lhs in
        let rel_vars = List.concat (List.map CP.fv rel_lhs) in

        DD.trace_hprint (add_str "lhs_p:" (!CP.print_formula)) lhs_p pos;
        DD.trace_hprint (add_str "lhs_p_memo:" (!CP.print_formula)) lhs_p_memo pos;
        DD.trace_hprint (add_str "lhs_h_p (lhs_h_mix):" (!CP.print_formula)) lhs_h_p pos;
        DD.trace_hprint (add_str "lhs (after lhs_simplifier):" (!CP.print_formula)) lhs pos;
        DD.trace_hprint (add_str "lhs_p_new (b4 filter ass):" (!CP.print_formula)) lhs_p_new pos;

        (* Begin - Auxiliary function *)
        let is_bag_cnt = TP.is_bag_constraint lhs in
        let filter_ass lhs rhs = 
          let is_sat = if is_bag_cnt then (fun x -> true) else is_sat in
          let (lhs,rhs) = rel_filter_assumption is_sat lhs rhs in
          (simplify_disj_new lhs,rhs) 
        in
        let pairwise_proc lhs =
          let lst = CP.split_conjunctions lhs in
          (* perform pairwise only for disjuncts *)
          let lst = List.map (fun e -> 
              if CP.is_disjunct e then TP.pairwisecheck e else e) lst 
          in CP.join_conjunctions lst
        in
        let wrap_exists (lhs,rhs) =
          let vs_r = CP.fv rhs in
          let vs_l = CP.fv lhs in
          (* To keep vars of RelForm _ that come from lhs *)
          let diff_vs = diff_svl vs_l (vs_r@rel_vars) in
          DD.tinfo_hprint (add_str "diff_vs" !print_svl) diff_vs pos;
          let new_lhs = CP.wrap_exists_svl lhs diff_vs in
          DD.tinfo_hprint (add_str "new_lhs (b4 elim_exists)" !CP.print_formula) new_lhs pos;
          let new_lhs,lhs_rel_list = 
            if is_bag_cnt then 
              (* TODO: The better is to avoid generating redundant primed vars *)
              pairwise_proc (CP.arith_simplify_new (CP.remove_red_primed_vars new_lhs)),rel_lhs
            else
              let new_lhs_drop_rel = TP.simplify_raw (CP.drop_rel_formula new_lhs) in
              let new_lhs_drop_rel = pairwise_proc new_lhs_drop_rel in
              DD.ninfo_hprint (add_str "rel_lhs(b4):" (pr_list !CP.print_formula)) rel_lhs pos;
              let rel_lhs_new = List.filter (fun x -> not(Gen.BList.mem_eq CP.equalFormula x rel_to_del)) rel_lhs in
              DD.ninfo_hprint (add_str "rel_lhs(af):" (pr_list !CP.print_formula)) rel_lhs_new pos;
              CP.conj_of_list (new_lhs_drop_rel::rel_lhs_new) no_pos,rel_lhs_new
          in
          DD.ninfo_hprint (add_str "new_lhs (aft elim_exists)" !CP.print_formula) new_lhs pos;
          (* Simplification steps *)
          let lhs_list = CP.split_disjunctions_deep new_lhs in
          let new_lhs_list = List.map (fun new_lhs_local ->
              Debug.tinfo_hprint (add_str "rel-defn:rhs" Cprinter.string_of_pure_formula) rhs no_pos;
              Debug.tinfo_hprint (add_str "rel-defn:new lhs" Cprinter.string_of_pure_formula) new_lhs_local no_pos;
              let new_lhs_local = filter_ante_wo_rel new_lhs_local rhs in
              Debug.tinfo_hprint (add_str "rel-defn:filter_ante lhs" Cprinter.string_of_pure_formula) new_lhs_local no_pos;
              let rec_lhs_rel_vars = List.filter (fun x -> CP.subset (CP.get_rel_id_list x) rel_rhs_n) lhs_rel_list in 
              let lhs_vars_wo_rel = CP.remove_dups_svl (List.concat (List.map CP.fv_wo_rel lhs_rel_list)) in
              let rhs_vars_wo_rel = CP.fv_wo_rel rhs in
              let lhs_vars_wo_rel = CP.diff_svl lhs_vars_wo_rel rhs_vars_wo_rel in
              let rhs_vars_wo_rel = rhs_vars_wo_rel @ List.concat(List.map CP.fv_wo_rel rec_lhs_rel_vars) in
              let lhs_als = MCP.ptr_equations_without_null (MCP.mix_of_pure new_lhs_local) in
              let lhs_aset = build_var_aset lhs_als in
              let subs_pairs = List.concat(List.map (fun r -> 
                  let als_set = CP.EMapSV.find_equiv_all r lhs_aset in
                  let needed_set = CP.intersect als_set lhs_vars_wo_rel in
                  List.map (fun elem -> (elem,r)) needed_set
              ) rhs_vars_wo_rel) in
              let new_lhs_local = CP.remove_redundant_constraints (CP.subst subs_pairs new_lhs_local) in
              (*            let new_lhs_local = if is_bag_cnt then new_lhs_local else*)
              (*              let rel_lhs,conj_wo_rel = List.partition CP.is_RelForm (CP.list_of_conjs new_lhs_local) in*)
              (*              let rel_lhs = if rec_lhs_rel_vars=[] then rel_lhs else *)
              (*                  let _ = DD.info_hprint (add_str "rel_lhs(b4):" (pr_list !CP.print_formula)) rel_lhs pos in*)
              (*                  let lhs_rec_vars = List.concat (List.map CP.fv conj_wo_rel) in*)
              (*                  DD.info_hprint (add_str "Rec vars " !print_svl) lhs_rec_vars pos;*)
              (*                  let rel_to_del = List.filter (fun x -> CP.intersect lhs_rec_vars (CP.fv x) = []) rec_lhs_rel_vars in*)
              (*                  let _ = DD.info_hprint (add_str "to del:" (pr_list !CP.print_formula)) rel_to_del pos in*)
              (*                  let res = List.filter (fun x -> not(Gen.BList.mem_eq CP.equalFormula x rel_to_del)) rel_lhs in*)
              (*                  DD.info_hprint (add_str "rel_lhs(af):" (pr_list !CP.print_formula)) res pos;*)
              (*                  res*)
              (*              in*)
              (*              CP.conj_of_list (conj_wo_rel@rel_lhs) pos*)
              new_lhs_local) lhs_list 
          in
          Debug.ninfo_hprint (add_str "simplified lhs" (pr_list !CP.print_formula)) new_lhs_list no_pos;
          (* Simplification steps -- End *)

          let rel_def_id = CP.get_rel_id_list rhs in
          (*          let rank_bnd_id = CP.get_rank_bnd_id_list rhs in*)
          (*          let rank_dec_id = CP.get_rank_dec_and_const_id_list rhs in*)
          let rel_cat = 
            if rel_def_id != [] then CP.RelDefn (List.hd rel_def_id) else 
              (*            if rank_bnd_id != [] then CP.RankBnd (List.hd rank_bnd_id) else*)
              (*            if rank_dec_id != [] then CP.RankDecr rank_dec_id else*)
              report_error pos "Relation belongs to unexpected category"
          in
          List.map (fun x -> (rel_cat,x,rhs)) new_lhs_list
        in
        (* End - Auxiliary function *)
        let inf_rel_ls = List.map (filter_ass lhs_p_new) rel_rhs in
        DD.trace_hprint (add_str "Rel Inferred (b4 pairwise):" (pr_list print_only_lhs_rhs)) inf_rel_ls pos;
        let inf_rel_ls = 
          if is_bag_cnt then 
            List.map (fun (lhs,rhs) -> (pairwise_proc lhs,rhs)) inf_rel_ls 
          else inf_rel_ls in
        DD.trace_hprint (add_str "Rel Inferred (b4 wrap_exists):" (pr_list print_only_lhs_rhs)) inf_rel_ls pos;
        let inf_rel_ls = List.concat (List.map wrap_exists inf_rel_ls) in
      	(* below causes non-linear LHS for relation *)
	(* let inf_rel_ls = List.map (simp_lhs_rhs vars) inf_rel_ls in *)
        (* DD.info_hprint (add_str "Rel Inferred (simplified)" (pr_list print_lhs_rhs)) inf_rel_ls pos; *)
        infer_rel_stk # push_list inf_rel_ls;
        Log.current_infer_rel_stk # push_list inf_rel_ls;
        let estate = { estate with es_infer_rel = estate.es_infer_rel@inf_rel_ls;} in
        if inf_rel_ls != [] then
          begin
            DD.devel_pprint ">>>>>> infer_collect_rel <<<<<<" pos;
            DD.tinfo_hprint (add_str "Infer Rel Ids" !print_svl) ivs pos;
            (* DD.devel_hprint (add_str "LHS heap Xpure1:" !print_mix_formula) lhs_h_mix pos; *)
            DD.tinfo_hprint (add_str "LHS pure" !CP.print_formula) lhs_p pos;
            DD.tinfo_hprint (add_str "RHS pure" !CP.print_formula) rhs_p pos;
            (* DD.tinfo_hprint (add_str "RHS pure" !CP.print_formula) rhs_p_n pos; *)
            DD.devel_hprint (add_str "Rel Inferred:" (pr_list print_lhs_rhs)) inf_rel_ls pos;
            DD.tinfo_hprint (add_str "RHS Rel List" (pr_list !CP.print_formula)) rel_rhs pos;
          end;
        (estate,lhs_mix,rhs_mix_new,None,[])
(*
Given:
infer vars:[n,R]
LHS heap Xpure1: x=null & n=0 | x!=null & 1<=n
LHS pure: x=null & rs=0
RHS pure R(rs,n) & x=null
(1) simplify LHS to:
     x=null & n=0 & rs=0
(2) partition RHS to 
    (a) R(rs,n)
    (b) x=null
(3) for inferred relation R, use filter
    assumption to obtain:
     (n=0 rs=0 --> R(rs,n)) to add to es_infer_rel 
*)


let infer_collect_rel is_sat estate lhs_h_mix lhs_mix rhs_mix pos =
  let pr0 = !print_svl in
  let pr1 = !print_mix_formula in
  let pr2 = !print_entail_state_short in 
  let pr_rel_ass = pr_list (fun (es,r,b) -> pr_pair pr2 (pr_list CP.print_lhs_rhs) (es,r)) in
  let pr_neg_lhs = pr_option (pr_pair pr2 !CP.print_formula) in
  let pr2 (es,l,r,p,a) = 
    pr_penta pr1 pr1 (pr_list CP.print_lhs_rhs) pr_neg_lhs pr_rel_ass (l,r,es.es_infer_rel,p,a) in
  Debug.no_4 "infer_collect_rel" pr0 pr1 pr1 pr1 pr2
    (fun _ _ _ _ -> 
      infer_collect_rel is_sat estate lhs_h_mix lhs_mix rhs_mix pos) 
    estate.es_infer_vars_rel lhs_h_mix lhs_mix rhs_mix

(******************************************************************************)
           (*=****************INFER REL HP ASS****************=*)
(*=*****************************************************************=*)

let generate_linking_svl_x drop_hpargs total_unk_map=
  let generate_linking_svl_one_hp pos (hp,args)=
    let hp_name = CP.name_of_spec_var hp in
    let ps,fr_svl,unk_map =
      try
          let fr_args = List.assoc hp total_unk_map in
          let ss = List.combine args fr_args in
          let ps = List.map (fun (sv,fr_sv) -> CP.mkPtrEqn sv fr_sv pos) ss in
          (ps,fr_args,[])
      with Not_found ->
          let ps,fr_svl = List.split (List.map (fun sv ->
              let fr_sv = CP.fresh_spec_var_prefix hp_name sv in
              (CP.mkPtrEqn sv fr_sv pos, fr_sv)
          ) args) in
          (ps,fr_svl,[(hp,fr_svl)])
    in
    let p = CP.conj_of_list ps pos in
    (p,fr_svl,unk_map)
  in
  let ps,ls_fr_svl,ls_unk_map = split3 (List.map (generate_linking_svl_one_hp no_pos) drop_hpargs) in
  (List.concat ls_fr_svl,CP.conj_of_list ps no_pos,List.concat ls_unk_map)

let generate_linking_svl drop_hpargs total_unk_map=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr2 = pr_triple !CP.print_svl !CP.print_formula
    (pr_list (pr_pair !CP.print_sv !CP.print_svl)) in
  Debug.no_1 "generate_linking_svl" pr1 pr2
      (fun _ -> generate_linking_svl_x drop_hpargs total_unk_map) drop_hpargs

let match_unk_preds prog lhs_hpargs rhs_hp rhs_args=
  let r_inst = SAU.get_inst_hp_args prog rhs_hp in
  let rec helper lhs_rest=
    match lhs_rest with
      | [] -> None
      | (hp,args)::rest ->
            if  List.length rhs_args = List.length args && CP.diff_svl rhs_args args = []
            then
              let l_inst = SAU.get_inst_hp_args prog hp in
              if SAU.cmp_inst l_inst r_inst then
                (Some (hp))
              else helper rest
            else helper rest
  in
  helper lhs_hpargs
(*
1.  H(x) --> x::node<_,p>: p is forwarded
2.  H(x,y) --> x::node<_,p>: p and y are forwarded
3.  x::<_,p> * H (p,p1) --> G(x): p and p1 are NOT forwarded
3a. z::node2<_,l,r> * HP_577(l) * G1(r) --> G1(z) : l,r are NOT forwarded
*)
let find_undefined_selective_pointers_x prog lfb lmix_f unmatched rhs_rest rhs_h_matched_set leqs reqs pos
      total_unk_map post_hps prog_vars=
  let get_rhs_unfold_fwd_svl h_node h_args def_svl lhs_hpargs=
    let rec parition_helper node_name hpargs=
      match hpargs with
        | [] -> (false, false, [],[])
        | (hp,args)::tl ->
              let i_args, ni_args = SAU.partition_hp_args prog hp args in
              let inter,rem = List.partition
                (fun (sv,_) -> CP.eq_spec_var node_name sv) i_args
              in
              if inter = [] then parition_helper node_name tl
              else
                let is_pre = Cast.check_pre_post_hp prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in
                (true, is_pre, rem, (ni_args))
    in
    let res,is_pre, niu_svl_i, niu_svl_ni = parition_helper h_node lhs_hpargs in
    if res then
      let args1 = CP.remove_dups_svl (CP.diff_svl h_args def_svl) in
      (* let _ = Debug.info_pprint ("     h_args:" ^(!CP.print_svl args1)) no_pos in *)
      (*old: args1@not_in_used_svl*)
      (*not_in_used_svl: NI*)
      let args11 = List.map (fun sv -> (sv, I)) args1 in
      let niu_svl_i_ni = List.map (fun (sv,_) -> (sv, NI)) niu_svl_i in
      let niu_svl_ni_total = niu_svl_i_ni@niu_svl_ni in
      let ls_fwd_svl = (List.map (fun sv -> (is_pre, sv::niu_svl_ni_total)) args11) in
      (*generate extra hp for cll*)
      let extra_clls = if niu_svl_i = [] then []
      else
        [(is_pre, niu_svl_i@[(h_node, NI)])]
      in
      (true,ls_fwd_svl@extra_clls)
    else (false, [])
  in
  let get_lhs_fold_fwd_svl selected_hps def_vs rhs_args lhs_hds
        lhs_hvs ls_lhs_hpargs=
    let rec find_pt_new cur_hds svl res hd_rest=
      match cur_hds with
        | [] -> res,hd_rest
        | hd::tl ->
            let ptr_args = List.filter CP.is_node_typ hd.CF.h_formula_data_arguments in
            if (CP.intersect_svl ptr_args (svl@res) <> []) then
              find_pt_new tl svl (res@[hd.CF.h_formula_data_node]) hd_rest
            else find_pt_new tl svl res (hd_rest@[hd])
    in
    let rec loop_helper hds svl r=
      let r1,rest = find_pt_new hds svl r [] in
      if CP.diff_svl r1 r = [] || rest = [] then r1 else
        loop_helper rest svl r1
    in
    let process_one (hp,args)=
      (* let _ = Debug.info_pprint ("  hp: " ^ (!CP.print_sv hp)) no_pos in *)
      if CP.mem_svl hp selected_hps then
        let args_ins,_ = SAU.partition_hp_args prog hp args in
        let args_ins1 = fst (List.split args_ins) in
        let opto = loop_helper (*find_pt_new*) lhs_hds args_ins1 [] in
        (match opto with
          | [] -> []
          | ptos -> begin
              (* let _ = Debug.info_pprint ("    ptos:" ^(!CP.print_svl ptos)) no_pos in *)
              (* let _ = Debug.info_pprint ("    rhs_args:" ^(!CP.print_svl rhs_args)) no_pos in *)
              if CP.intersect_svl ptos rhs_args <> [] then [] else
                let fwd_svl = CP.remove_dups_svl (CP.diff_svl args_ins1 (def_vs@rhs_args)) in
                (* let is_pre = Cast.check_pre_post_hp prog.Cast.prog_hp_decls (CP.name_of_spec_var hp) in *)
                ((* is_pre, *) fwd_svl)
            end
        )
      else []
    in
    let ls_not_fwd_svl = List.map process_one ls_lhs_hpargs in
    (*should separate list of list *)
    (* let ls_not_fwd_svl1 = CP.remove_dups_svl (fun (_,svl1) (_,svl2) -> *)
    (*     List.length svl1 = List.length svl2 *)
    (*         && (CP.diff_svl svl1 slv2 = []) ) ls_not_fwd_svl in *)
    let ls_not_fwd_svl1 = CP.remove_dups_svl (List.concat ls_not_fwd_svl) in
    (*TODO: *)
    let ls_not_fwd_svl1_inst = List.map (fun sv -> (sv, I)) ls_not_fwd_svl1 in
    (true, ls_not_fwd_svl1_inst)
  in
  (* DD.info_pprint ">>>>>> find_undefined_selective_pointers <<<<<<" pos; *)
  (* let lfb = CF.subst_b leqs lfb in *)
  (* let rfb = CF.subst_b leqs rfb in *)
  let n_unmatched = (* CF.h_subst leqs *) unmatched in
  let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lfb in
  let leqNulls = MCP.get_null_ptrs lmix_f in
  let rhds, rhvs, rhrs = CF.get_hp_rel_h_formula n_unmatched in
  let reqNulls = [] (* MCP.get_null_ptrs rmix_f *) in
  (* let hrs = (lhrs @ rhrs) in *)
  let hds = (lhds @ rhds) in
  let hvs = (lhvs @ rhvs) in
  let eqs = (leqs@reqs) in
   (*defined vars=  null + data + view + match nodes*)
  let r_def_vs = reqNulls @ (List.map (fun hd -> hd.CF.h_formula_data_node) rhds)
   @ (List.map (fun hv -> hv.CF.h_formula_view_node) rhvs) in
  (*selective*)
  (*START debugging*)
  let _ = DD.ninfo_pprint (" n_lfb: " ^ (Cprinter.string_of_formula_base lfb)) pos in
  let _ = DD.ninfo_pprint (" n_unmatched: " ^ (Cprinter.string_of_h_formula n_unmatched)) pos in
  (*END debugging*)
  (* let n_lhds, _, n_lhrs = CF.get_hp_rel_bformula n_lfb in *)
  (**********get well-defined hp in lhs*)
  let helper (hp,eargs,_)=(hp,List.concat (List.map CP.afv eargs)) in
  let ls_lhp_args = (List.map helper lhrs) in
  let ls_rhp_args = (List.map helper rhrs) in
  let r_hps = List.map fst ls_rhp_args in
  let l_def_vs = leqNulls @ (List.map (fun hd -> hd.CF.h_formula_data_node) lhds)
   @ (List.map (fun hv -> hv.CF.h_formula_view_node) lhvs) in
  let l_def_vs = CP.remove_dups_svl (CF.find_close l_def_vs (eqs)) in
  (*ll-append9-10: if not generate linking here, we can not obtain it later*)
  (* let unk_svl, unk_xpure, unk_map1 = (\* if !Globals.sa_split_base then *\) *)
  (*   SAC.generate_linking total_unk_map ls_lhp_args ls_rhp_args (\*eqs*\) post_hps pos *)
  (* (\* else ([], CP.mkTrue pos,total_unk_map) *\) *)
  (* in *)
  let unk_svl = [] in
  let unk_xpure = CP.mkTrue pos in
  let unk_map1 = [] in
  (* let lfb1 = CF.mkAnd_base_pure lfb (MCP.mix_of_pure unk_xpure) pos in *)
  let lfb, defined_hps,rem_lhpargs, new_lhs_hps =
    if r_hps = [] || CP.diff_svl r_hps post_hps <> [] then (lfb, [], ls_lhp_args, []) else
    List.fold_left (fun (lfb0,ls_defined,ls_rem, ls_new_hps) hpargs ->
        let lfb1, r_def,r_mem, new_hps = SAU.find_well_defined_hp prog lhds lhvs r_hps
          prog_vars post_hps hpargs l_def_vs lfb0 false pos in
        (lfb1, ls_defined@r_def,ls_rem@r_mem, ls_new_hps@new_hps)
    ) (lfb, [],[], []) ls_lhp_args
  in
  (*END************get well-defined hp in lhs*)
  let def_vs = l_def_vs@r_def_vs in
  (*find closed defined pointers set*)
  let def_vs = CP.remove_dups_svl (CF.find_close def_vs (eqs)) in
  (*remove*)
  (* let unmatched_svl = (SAU.get_ptrs unmatched) in *)
  let unmatched_svl = (SAU.get_root_ptrs prog unmatched) in
  let unmatched_svl = (CF.find_close (unmatched_svl) (eqs)) in
  let closed_unmatched_svl0 = SAU.look_up_closed_ptr_args prog hds hvs unmatched_svl
     (* List.concat (List.map (SAU.look_up_ptr_args_one_node prog hds hvs) unmatched_svl) *)
  in
  let closed_unmatched_svl = CP.remove_dups_svl
    (CF.find_close  (CP.remove_dups_svl (unmatched_svl@closed_unmatched_svl0)) (eqs)) in
  let _ = Debug.ninfo_pprint ("    closed_unmatched_svl:" ^(!CP.print_svl closed_unmatched_svl)) no_pos in
  (*END selective*)
  (*get all args of hp_rel to check whether they are fully embbed*)
  (* let unmatched_hp_args = CF.get_HRels n_unmatched in *)
  let selected_hp_args = List.filter (fun (hp, args) ->
      let args_inst = SAU.get_hp_args_inst prog hp args in
      (CP.intersect_svl args_inst closed_unmatched_svl) != []) rem_lhpargs in
  let selected_hps0, hrel_args = List.split selected_hp_args in
  (*tricky here: do matching between two unk hps and we keep sth in rhs which not matched*)
  let rest_svl = CF.get_hp_rel_vars_h_formula rhs_rest in
  let rest_svl1 = CF.find_close rest_svl leqs in
  let select_helper svl (hp,args)=
    if CP.diff_svl args svl = [] then [(hp,args)]
    else []
  in
  let drop_hpargs =  List.concat (List.map (select_helper rest_svl1) ls_lhp_args) in
  let drop_hps =  (List.map fst drop_hpargs) in
  let selected_hpargs =
    List.filter (fun (hp,_) -> not (CP.mem_svl hp drop_hps)) selected_hp_args
  in
  (*========*)
  (*find undefined ptrs of all hrel args*)
  (*two cases: rhs unfold (mis-match is a node) and lhs fold (mis-match is a unk hp)*)
  let mis_match_found, ls_fwd_svl,rhs_sel_hpargs,lhs_selected_hpargs =
    if CF.is_HRel n_unmatched then
      let rhs_hp, rhs_args= CF.extract_HRel n_unmatched in
      (*depend on the purpose of geting framing spec*)
      (*svl: framing heap*)
      let svl,selected_hpargs0 = (* if proving_kind#string_of = "POST" then [] else *)
      (*since h_subst is not as expected we use closed set*)
        match match_unk_preds prog ls_lhp_args rhs_hp rhs_args with
          | Some hp ->
                ([], [(hp,rhs_args)])
          | None ->
                let closed_rhs_hpargs = CF.find_close rhs_args leqs in
                let r1,r2 = (get_lhs_fold_fwd_svl (List.map fst selected_hpargs) def_vs closed_rhs_hpargs lhds lhvs ls_lhp_args,
                selected_hpargs) in
                ([r1],r2)
      in
       (* let closed_svl = CF.find_close svl leqs in *)
       DD.ninfo_pprint ("svl: " ^ ((pr_list (pr_pair string_of_bool (pr_list (pr_pair !CP.print_sv print_arg_kind)))) svl)) pos;
      (*let unk_svl, unk_xpure, unk_map1 =*)
      (true (*TODO*), svl,[(rhs_hp, rhs_args)],selected_hpargs0)
    else
      let h_node, h_args = SAU.get_h_node_cont_args_hf prog n_unmatched in
      let h_args1 = List.filter CP.is_node_typ h_args in
      let hrel_args1 = List.concat hrel_args in
      (*should include their closed ptrs*)
      let hrel_args2 = CP.remove_dups_svl (List.fold_left SAU.close_def hrel_args1 (eqs)) in
      let mis_match_found, ls_unfold_fwd_svl = get_rhs_unfold_fwd_svl h_node h_args1 (def_vs@hrel_args2) ls_lhp_args in
      (mis_match_found, ls_unfold_fwd_svl(* @lundefs_args *),[],selected_hpargs)
  in
  let ls_undef =  (* List.map CP.remove_dups_svl *) (ls_fwd_svl) in
  (* DD.info_pprint ("selected_hpargs: " ^ (let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in pr (selected_hpargs))) pos; *)
  let ls_defined_hpargs =  List.map (fun (hp,args,_,_) -> (hp,args)) defined_hps in
  let lhs_selected_hpargs0 = List.filter (fun (hp,args) ->
      not (Gen.BList.mem_eq SAU.check_hp_arg_eq (hp,args) ls_defined_hpargs)
  ) lhs_selected_hpargs
  in
  (mis_match_found, (* undefs1@lundefs_args *) ls_undef,hds,hvs,lhrs,rhrs,leqNulls@reqNulls, lhs_selected_hpargs0,rhs_sel_hpargs, defined_hps,
  CP.remove_dups_svl (unk_svl),unk_xpure,unk_map1,new_lhs_hps)

let find_undefined_selective_pointers prog lfb lmix_f unmatched rhs_rest rhs_h_matched_set leqs reqs pos
      total_unk_map post_hps prog_vars=
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 = Cprinter.prtt_string_of_h_formula in
  let pr3 = pr_list (pr_pair !CP.print_sv !print_svl) in
  let pr4 = pr_list (pr_pair string_of_bool (pr_list (pr_pair !CP.print_sv print_arg_kind))) in
  let pr6 = pr_list_ln (pr_quad !CP.print_sv !CP.print_svl pr1 Cprinter.prtt_string_of_formula) in
  (* let pr7 = pr_list (pr_pair (pr_list (pr_pair !CP.print_sv string_of_int)) CP.string_of_xpure_view) in *)
  let pr7 = (pr_list (pr_pair (pr_pair !CP.print_sv (pr_list string_of_int)) CP.string_of_xpure_view)) in
  let pr5 = fun (is_found, undefs,_,_,_,_,_,selected_hpargs, rhs_sel_hpargs,defined_hps,_,_,unk_map,_) ->
      let pr = pr_hexa string_of_bool pr4 pr3 pr3 pr6 pr7 in
      pr (is_found, undefs,selected_hpargs,rhs_sel_hpargs, defined_hps, unk_map)
  in
  Debug.no_3 "find_undefined_selective_pointers" 
      (add_str "unmatched" pr2) 
      (add_str "rhs_h_matched_set" !print_svl) 
      (add_str "lfb" pr1)
      pr5
      ( fun _ _ _ -> find_undefined_selective_pointers_x prog lfb lmix_f unmatched rhs_rest
    rhs_h_matched_set leqs reqs pos total_unk_map post_hps prog_vars) unmatched rhs_h_matched_set lfb


(*
out: list of program variables of mismatching node
*)
let get_prog_vars_x prog_hps rhs_unmatch proving_kind =
  match rhs_unmatch with
    | CF.HRel (hp, eargs,_) ->
        if proving_kind = "POST" && CP.mem_svl hp prog_hps then
          ([hp],(List.fold_left List.append [] (List.map CP.afv eargs)))
        else [],[]
    | _ -> [],[]

let get_prog_vars prog_hps rhs_unmatch proving_kind =
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.string_of_h_formula in
  let pr3 s= s (* Log.string_of_sleek_proving_kind *) in
  Debug.no_3 "get_prog_vars" pr1 pr2 pr3 (pr_pair pr1 pr1)
      (fun _ _ _ -> get_prog_vars_x prog_hps rhs_unmatch proving_kind) prog_hps rhs_unmatch proving_kind

let get_history_nodes_x root_svl hds history lfb done_args eqs lhs_hpargs=
  let hd_names = List.map (fun hd -> hd.CF.h_formula_data_node) hds in
  let hd_closed_names = (List.fold_left SAU.close_def hd_names eqs) in
  let undefined_ptrs = Gen.BList.difference_eq CP.eq_spec_var root_svl hd_closed_names in
  (* let _ = Debug.info_pprint ("      undefined_ptrs: " ^ (!CP.print_svl  undefined_ptrs)) no_pos in *)
  let pos = CF.pos_of_formula (CF.Base lfb) in
  let rec look_up cur_hds dn0=
    match cur_hds with
      | [] -> []
      | dn1::hdss -> if CP.eq_spec_var dn1.CF.h_formula_data_node dn0.CF.h_formula_data_node then
            List.combine dn0.CF.h_formula_data_arguments dn1.CF.h_formula_data_arguments
          else look_up hdss dn0
  in
  let rec lookup_hrel ls_hpargs (hp0,args0)=
    match ls_hpargs with
      | [] -> false
      | (hp,args)::tl ->
          if CP.eq_spec_var hp0 hp then
            let args1 = List.map ((CP.subs_one eqs)) args in
            let args01 = List.map ((CP.subs_one eqs)) args0 in
            if SAU.eq_spec_var_order_list args1 args01 then true else
              lookup_hrel tl (hp0,args0)
          else lookup_hrel tl (hp0,args0)
  in
  let helper (fb,hps,keep_svl,r_ss) hf=
    match hf with
      | CF.DataNode dn ->
          if CP.mem_svl dn.CF.h_formula_data_node undefined_ptrs then
            (mkAnd_fb_hf fb hf pos,hps,keep_svl,r_ss)
          else
            let ss = look_up hds dn in
            (fb,hps,keep_svl,r_ss@ss)
      | CF.HRel (hp,eargs,p) ->
          let args = List.concat (List.map CP.afv eargs) in
          if (Gen.BList.intersect_eq CP.eq_spec_var args undefined_ptrs) = [] ||
            (Gen.BList.difference_eq CP.eq_spec_var args done_args) = [] ||
             lookup_hrel lhs_hpargs (hp,args)
          then
            (fb,hps,keep_svl,r_ss)
          else
            (mkAnd_fb_hf fb hf p,hps@[hp], keep_svl@(Gen.BList.difference_eq CP.eq_spec_var args undefined_ptrs),r_ss)
      | HEmp -> (fb,hps,keep_svl,r_ss)
      | _ -> report_error pos "infer.get_history_nodes"
  in
  List.fold_left helper (lfb,[],[],[]) history

let get_history_nodes root_svl hds history lfb done_args eqs lhs_hpargs=
  let pr1 = pr_list_ln Cprinter.string_of_h_formula in
  let pr2 = Cprinter.string_of_formula_base in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr4 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_4 "get_history_nodes" !CP.print_svl pr1 pr2 pr4 (fun (f,_,_,ss) ->(pr2 f) ^ " ;ss: " ^ (pr3 ss))
      (fun _ _ _ _ -> get_history_nodes_x root_svl hds history lfb done_args eqs lhs_hpargs) root_svl history lfb lhs_hpargs

let get_h_formula_data_fr_hnode hn=
  match hn with
    | CF.DataNode hd -> [hd]
    | CF.HEmp -> []
    | CF.HRel _ -> []
    | _ -> report_error no_pos
        "infer.get_h_formula_data_fr_hnode: input must be a list of hnodes"


(*history from func calls*)
let simplify_lhs_rhs prog lhs_b rhs_b leqs reqs hds hvs lhrs rhrs lhs_selected_hpargs rhs_selected_hpargs
      crt_holes history unk_svl prog_vars=
  let look_up_lhs_i_var (hp,args)=
    (* let _ = Debug.info_pprint ("    args:" ^ (!CP.print_svl hd) ^ ": "^(!CP.print_svl args)) no_pos in *)
    let i_args_w_inst,_ = SAU.partition_hp_args prog hp args in
    List.map fst i_args_w_inst
  in
  let filter_non_selected_hp selected_hpargs (hp,args)= Gen.BList.mem_eq SAU.check_hp_arg_eq (hp,args) selected_hpargs in
  let filter_non_selected_hp_rhs selected_hps (hp,_)= CP.mem_svl hp selected_hps in
  (*lhs*)
  let l_hpargs = List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs)) ) lhrs in
  let _,l_rem_hp_args = (List.partition (filter_non_selected_hp lhs_selected_hpargs) l_hpargs) in
  let lhp_args = lhs_selected_hpargs in
  let lkeep_hrels,lhs_keep_rootvars = List.split lhp_args in
  let lhs_keep_rootvars = List.concat lhs_keep_rootvars in
  let lhs_keep_i_rootvars = List.fold_left (fun ls (hp,args) -> ls@(look_up_lhs_i_var (hp,args))) [] lhp_args in
  (*rhs*)
  let rhs_selected_hps = List.map fst rhs_selected_hpargs in
  let r_hpargs = CF.get_HRels rhs_b.CF.formula_base_heap in
  let rhp_args,r_rem_hp_args = (List.partition (filter_non_selected_hp_rhs rhs_selected_hps) r_hpargs) in
  (*root of hprel is the inst args*)
  let rkeep_hrels, rhs_keep_rootvars = List.fold_left (fun (hps,r_args) (hp,args) ->
      (hps@[hp], r_args@(look_up_lhs_i_var (hp,args)))
  ) ([],[]) rhp_args in
  (***************************)
  (*w history*)
  let svl = (CP.remove_dups_svl (lhs_keep_i_rootvars@rhs_keep_rootvars)) in
  let svl = (List.fold_left SAU.close_def svl (leqs@reqs)) in
  (*get args which already captures by other hprel*)
  let done_args = CP.remove_dups_svl (List.concat (List.map (fun (_,args) -> args) (lhp_args))) in
  let lhs_b,history_hrel,keep_root_hrels,his_ss = get_history_nodes svl hds history lhs_b done_args (leqs@reqs) lhp_args in
  (*END*)
  let rec elim_redun_his his res=
    match his with
      | [] -> res
      | hd:: tl ->
          let svl0 = CF.find_close [hd.CF.h_formula_data_node] leqs in
          if List.exists
            (fun hd1 -> CP.mem_svl hd1.CF.h_formula_data_node svl0) hds then
            elim_redun_his tl res
          else elim_redun_his tl (res@[hd])
  in
  let filter_his = elim_redun_his (List.concat (List.map get_h_formula_data_fr_hnode history)) [] in
  (* let _ = Debug.info_pprint ("    prog_vars:" ^(!CP.print_svl prog_vars)) no_pos in *)
  let lhs_b1,rhs_b1 = SAU.keep_data_view_hrel_nodes_two_fbs prog lhs_b rhs_b
    (hds@filter_his) hvs (lhp_args@rhp_args) leqs reqs [] (svl@keep_root_hrels) (lhs_keep_rootvars@keep_root_hrels)
   lhp_args rhs_selected_hps rhs_keep_rootvars unk_svl (CP.remove_dups_svl prog_vars) in
  (***************************)
  (*subst holes*)
  let lhs_b1 = {lhs_b1 with CF.formula_base_heap = IMM.apply_subs_h_formula crt_holes lhs_b1.CF.formula_base_heap} in
  let rhs_b1 = {rhs_b1 with CF.formula_base_heap = IMM.apply_subs_h_formula crt_holes rhs_b1.CF.formula_base_heap} in
  let lhs_b2 = (* CF.subst_b (leqs) *) lhs_b1 in (*m_apply_par*)
  let rhs_b2 = (* CF.subst_b (leqs@reqs) *) rhs_b1 in
  let _ = Debug.ninfo_pprint ("lhs_b1: " ^ (Cprinter.string_of_formula_base lhs_b1)) no_pos in
  let _ = Debug.ninfo_pprint ("rhs_b2: " ^ (Cprinter.string_of_formula_base rhs_b2)) no_pos in
  (*remove redundant: x=x*)
  let lhs_b3 = {lhs_b2 with CF.formula_base_pure = MCP.mix_of_pure
      (CP.remove_redundant (MCP.pure_of_mix lhs_b2.CF.formula_base_pure))} in
  let rhs_b3 = {rhs_b2 with CF.formula_base_pure = MCP.mix_of_pure
      (CP.remove_redundant (MCP.pure_of_mix rhs_b2.CF.formula_base_pure))} in
  (*args of one hp must be diff --
       inside SAU.keep_data_view_hrel_nodes_two_fbs*)
  (* let lhs_b4,rhs_b4 = SAU.rename_hp_args lhs_b3 rhs_b3 in *)
  (CF.prune_irr_neq_formula prog_vars lhs_b3 rhs_b,rhs_b3)

let simplify_lhs_rhs prog lhs_b rhs_b leqs reqs hds hvs lhrs rhrs
      lhs_selected_hpargs rhs_selected_hpargs crt_holes history unk_svl prog_vars =
  let pr = Cprinter.string_of_formula_base in
  DD.no_2 "simplify_lhs_rhs" pr pr (pr_pair pr pr) (fun _ _ -> simplify_lhs_rhs prog lhs_b rhs_b
      leqs reqs hds hvs lhrs rhrs lhs_selected_hpargs rhs_selected_hpargs crt_holes
      history unk_svl prog_vars) lhs_b rhs_b


let lookup_eq_hprel_ass_x hps hprel_ass lhs rhs=
  let lhs_svl = List.map (CP.name_of_spec_var) (CP.remove_dups_svl (CF.fv lhs)) in
  let rec checkeq_hprel hprels=
    match hprels with
      | [] -> false,[]
      | ass::tl ->
          let b1,_ = Checkeq.checkeq_formulas lhs_svl lhs ass.CF.hprel_lhs in
          if b1 then
            let b2,m = Checkeq.checkeq_formulas [] rhs ass.CF.hprel_rhs in
            if b2 then
              true,List.filter (fun (sv1,sv2) -> CP.mem sv1 hps) (List.hd m)
            else checkeq_hprel tl
          else
            checkeq_hprel tl
  in
   checkeq_hprel hprel_ass

(*example s3*)
let lookup_eq_hprel_ass hps hprel_ass lhs rhs=
  let pr1 = pr_list_ln Cprinter.string_of_hprel in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr4 = pr_pair string_of_bool pr3 in
  Debug.no_4 "lookup_eq_hprel_ass" !CP.print_svl pr1 pr2 pr2 pr4
      (fun _ _ _ _ -> lookup_eq_hprel_ass_x hps hprel_ass lhs rhs) hps hprel_ass lhs rhs

let constant_checking prog rhs lhs_b rhs_b es=
  let r,new_lhs = SAU.simp_matching prog (CF.Base lhs_b) (CF.Base rhs_b) in
  if r then
    let new_es = {es with CF.es_formula = new_lhs} in
    (true, new_es, rhs, None)
  else
    (false, es, rhs, None)


let generate_constraints prog es rhs lhs_b rhs_b1 defined_hps
      ls_unknown_ptrs unk_pure unk_svl no_es_history lselected_hpargs rselected_hpargs
      hds hvs lhras lhrs rhras rhrs leqs reqs eqNull prog_vars pos =
  let update_fb (fb,r_hprels,hps,hfs) (is_pre, unknown_ptrs) =
    match unknown_ptrs with
      | [] -> (fb,r_hprels,hps,hfs)
      | _ ->
            let (hf,vhp_rels) = SAU.add_raw_hp_rel prog is_pre unknown_ptrs pos in
            begin
              match hf with
                | HRel hp ->
                      ((CF.mkAnd_fb_hf fb hf pos), r_hprels@[vhp_rels],
                      hps@[hp], hfs@[hf])
                | _ -> report_error pos "infer.generate_constraints: add_raw_hp_rel should return a hrel"
            end
  in
  (* let new_lhs = rhs_b1 in *)
  let new_rhs_b,rvhp_rels,new_hrels,r_new_hfs =
    List.fold_left update_fb (rhs_b1,[],[],[]) ls_unknown_ptrs in
  (*add roots from history*)
  let matched_svl = CF.get_ptrs (*es.CF.es_heap*) lhs_b.CF.formula_base_heap in
  let matched_svl1 = (List.fold_left SAU.close_def matched_svl (leqs@reqs)) in
  let sel_his = List.concat (List.map (fun hf -> match hf with
    | CF.DataNode hd -> if CP.mem_svl hd.CF.h_formula_data_node matched_svl1 then [] else [hf]
    | _ -> [hf]
  ) no_es_history) in
  DD.ninfo_pprint ("  new_rhs_b: " ^ (Cprinter.string_of_formula_base new_rhs_b)) pos;
  let lhs_b0 = CF.mkAnd_base_pure lhs_b (MCP.mix_of_pure unk_pure) pos in
  let group_unk_svl = List.concat (List.map (fun ass -> ass.CF.unk_svl) Log.current_hprel_ass_stk # get_stk) in
  let total_unk_svl = CP.remove_dups_svl (group_unk_svl@unk_svl) in
  let new_rhs_b0 = {new_rhs_b with 
              CF.formula_base_heap =  CF.check_imm_mis rhs new_rhs_b.CF.formula_base_heap} in
  let (new_lhs_b,new_rhs_b) = simplify_lhs_rhs prog lhs_b0 new_rhs_b0 leqs reqs hds hvs lhras (rhras@new_hrels)
    (lselected_hpargs) (rselected_hpargs@(List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs)))
        new_hrels)) es.CF.es_crt_holes ((* es.CF.es_heap:: *)(*no_es_history*) sel_his)
    total_unk_svl prog_vars in
  (*simply add constraints: *)
  let hprel_def = List.concat (List.map CF.get_ptrs (no_es_history@(CF.get_hnodes lhs_b.CF.formula_base_heap
      (* es.CF.es_heap *)))) in
  (* let closed_hprel_def = CP.subst_var_list (leqs@reqs) hprel_def in *)
  (* let closed_hprel_args_def,_,_,_,_ = SAU.find_defined_pointers_after_preprocess prog closed_hprel_def *)
  (*   (hds@(List.concat (List.map get_h_formula_data_fr_hnode no_es_history))) *)
  (*   hvs (lhras@rhras@new_hrels) (leqs@reqs) eqNull [] in *)
  (*split the constraints relating between pre- andxs post-preds*)
  (* let rf = CF.mkTrue (CF.mkTrueFlow()) pos in *)
  let defined_hprels = List.map (SAU.generate_hp_ass [] (* (closed_hprel_args_def@total_unk_svl) *) ) defined_hps in
  (*lookup to check redundant*)
  let new_lhs = CF.Base new_lhs_b in
  let new_rhs = CF.Base new_rhs_b in
  DD.ninfo_hprint (add_str "new_lhs" Cprinter.string_of_formula) new_lhs no_pos;
  DD.ninfo_hprint (add_str "new_rhs" Cprinter.string_of_formula) new_rhs no_pos;
  let b,m = if rvhp_rels = [] then (false,[]) else
    let ass = if rel_ass_stk # is_empty then [] else
      [(rel_ass_stk # top)]
    in
    lookup_eq_hprel_ass rvhp_rels ass new_lhs new_rhs
  in
  let hp_rels=
    if b && m <> [] then [] else
      [{
          CF.hprel_kind = CP.RelAssume (CP.remove_dups_svl (lhrs@rhrs@rvhp_rels));
          unk_svl = [] ;
          unk_hps = [];
          predef_svl = matched_svl ; (*(closed_hprel_args_def@total_unk_svl@matched_svl);*)
          hprel_lhs = CF.remove_neqNull_svl matched_svl (CF.Base new_lhs_b);
          hprel_rhs = CF.Base new_rhs_b;
      }]
  in
  let hp_rel_list = hp_rels@defined_hprels in
  let _ = rel_ass_stk # push_list (hp_rel_list) in
  let _ = Log.current_hprel_ass_stk # push_list (hp_rel_list) in
  let _ = DD.tinfo_pprint ("  hp_rels: " ^ (let pr = pr_list_ln Cprinter.string_of_hprel in pr hp_rels)) pos in
  let _ = DD.tinfo_pprint ("  hp_rel_list: " ^ (let pr = pr_list_ln Cprinter.string_of_hprel in pr hp_rel_list)) pos in
  r_new_hfs, new_lhs_b,m,rvhp_rels,hp_rel_list


let update_es prog es hds hvs ass_lhs_b rhs rhs_rest r_new_hfs defined_hps lselected_hpargs0
      rvhp_rels leqs m post_hps unk_map hp_rel_list pos=
   let update_es_f f new_hf=
    (CF.mkAnd_f_hf f (CF.h_subst leqs new_hf) pos)
   in
   begin
     let new_es_formula =  List.fold_left update_es_f es.CF.es_formula r_new_hfs in
     (*drop hp rel + nodes consumed in lhs of hp_rel in es_formula*)
     (* DD.info_pprint ("  before: " ^ (Cprinter.string_of_formula new_es_formula)) pos; *)
     let root_vars_ls = SAU.get_data_view_hrel_vars_bformula ass_lhs_b in
     (*tricky here: since we dont have matching between two unk hps, we keep sth in rhs which not matched*)
     let rest_svl = CF.get_hp_rel_vars_h_formula rhs_rest in
     let rest_svl1 = CF.find_close rest_svl leqs in
     let ass_hp_args = CF.get_HRels ass_lhs_b.CF.formula_base_heap in
     let check_full_inter svl (hp,args)=
       if CP.diff_svl args svl = [] then [hp] else []
     in
     let keep_hps =  List.concat (List.map (check_full_inter rest_svl1) ass_hp_args) in
     let _ = DD.ninfo_pprint ("  rest_svl: " ^ (!CP.print_svl rest_svl)) pos in
     let _ = DD.tinfo_pprint ("  keep_hps: " ^ (!CP.print_svl keep_hps)) pos in
     let root_vars_ls1 = CP.diff_svl root_vars_ls keep_hps in
     let well_defined_svl = List.concat (List.map (fun (hp,args,_,_) -> hp::args) defined_hps) in
     let root_vars_ls2 = CF.find_close root_vars_ls1 leqs in
     (*lhs should remove defined hps + selected hps*)
     let lselected_hpargs1 = lselected_hpargs0@(List.map (fun (a,b,_,_) -> (a,b)) defined_hps) in
     (*should consider closure of aliasing. since constraints are in normal form,
       but residue is not. and we want to drop exact matching of args*)
     let lselected_hpargs2 = List.map (fun (hp,args) -> (hp, CF.find_close args leqs)) lselected_hpargs1 in
     let _ = DD.ninfo_pprint ("  lselected_hpargs2: " ^ (let pr = pr_list (pr_pair !CP.print_sv  !CP.print_svl) in
        pr lselected_hpargs2)) pos
     in
     let _ = DD.ninfo_pprint ("  root_vars_ls2: " ^ (!CP.print_svl root_vars_ls2)) pos in
     let _ = DD.ninfo_pprint ("  before: " ^ (Cprinter.string_of_formula new_es_formula)) pos in
     let new_es_formula = SAU.drop_data_view_hrel_nodes_from_root prog new_es_formula hds hvs leqs root_vars_ls2
       well_defined_svl (CF.h_fv rhs) lselected_hpargs2 in
     let _ = DD.ninfo_pprint ("  after: " ^ (Cprinter.string_of_formula new_es_formula)) pos in
     (*CF.drop_hrel_f new_es_formula lhrs in *)
     (*add mismatched heap into the entail states if @L*)
     let check_consumed_node h f=
       match h with
         | DataNode hd -> 
               if (!Globals.allow_field_ann) then
                 (f,h)
               else 
                 if  not(CF.isLend (hd.CF.h_formula_data_imm)) then (f,h) else
                   let n_param_imm = List.map (fun _ -> CF.ConstAnn Mutable) hd.CF.h_formula_data_param_imm in
                   let new_h = DataNode {hd with CF.h_formula_data_imm = (CF.ConstAnn(Mutable));
                       CF.h_formula_data_param_imm = n_param_imm} in
                   (CF.mkAnd_f_hf f new_h pos, new_h)
         | _ -> (f,h)
     in
     let new_es_formula, new_rhs = check_consumed_node rhs new_es_formula in
     let new_es_formula1 = CF.subst m new_es_formula in
     let new_es = {es with CF. es_infer_vars_hp_rel = es.CF.es_infer_vars_hp_rel@rvhp_rels;
         CF.es_infer_hp_rel = es.CF.es_infer_hp_rel @ hp_rel_list;
         CF.es_infer_hp_unk_map = (es.CF.es_infer_hp_unk_map@unk_map);
         CF.es_infer_vars_sel_post_hp_rel = (es.CF.es_infer_vars_sel_post_hp_rel @ post_hps);
         CF.es_formula = new_es_formula1} in
     DD.tinfo_pprint ("  new residue: " ^ (Cprinter.string_of_formula new_es.CF.es_formula)) pos;
     let new_lhs = CF.convert_hf_to_mut new_rhs in
     (new_es, new_lhs)
   end

(*
type: Cast.prog_decl ->
  Cformula.entail_state ->
  SAU.CF.h_formula ->
  CP.spec_var list ->
  CF.formula_base -> CF.formula_base -> Globals.loc -> bool * CF.entail_st
*)
let infer_collect_hp_rel_x prog (es:entail_state) rhs rhs_rest (rhs_h_matched_set:CP.spec_var list) lhs_b rhs_b pos =
  (*for debugging*)
  (* DD.info_pprint ("  es: " ^ (Cprinter.string_of_formula es.CF.es_formula)) pos; *)
  let _ = Debug.ninfo_pprint ("es_infer_vars_hp_rel: " ^ (!CP.print_svl  es.es_infer_vars_hp_rel)) no_pos in
  let _ = Debug.ninfo_pprint ("es_infer_vars: " ^ (!CP.print_svl  es.es_infer_vars)) no_pos in
  let _ = Debug.ninfo_pprint ("es_infer_vars_sel_hp_rel: " ^ (!CP.print_svl  es.es_infer_vars_sel_hp_rel)) no_pos in
  (*end for debugging*)
  if no_infer_hp_rel es then
    constant_checking prog rhs lhs_b rhs_b es
        (* let r,new_lhs = SAU.simp_matching prog (CF.Base lhs_b) (CF.Base rhs_b) in *)
        (* if r then *)
        (*   let new_es = {es with CF.es_formula = new_lhs} in *)
        (*   (true, new_es) *)
        (* else *)
        (* (false, es) *)
  else
    let ivs = es.es_infer_vars_hp_rel in
    (*check whether LHS/RHS contains hp_rel*)
    (*ll-del-1*)
    let lhrs = CF.get_hp_rel_name_bformula lhs_b in
    let rhrs = CF.get_hp_rel_name_bformula rhs_b in
    if CP.intersect ivs (lhrs@rhrs) = [] then
      begin
        (* DD.info_pprint ">>>>>> infer_hp_rel <<<<<<" pos; *)
        let _ = DD.tinfo_pprint " no hp_rel found" pos in
        constant_checking prog rhs lhs_b rhs_b es
            (* (false,es) *)
      end
    else
      begin
        (*renaming: bug-app3.slk*)
        let v_lhs = (CF.fv (CF.Base lhs_b)) in
        let v_rhs = (CF.h_fv (rhs)) in
        let v_hp_rel = es.CF.es_infer_vars_hp_rel in
        let v_2_rename = Gen.BList.difference_eq CP.eq_spec_var v_rhs (v_lhs@v_hp_rel) in
        let fr_svl = CP.fresh_spec_vars v_2_rename in
        let sst0 = List.combine v_2_rename fr_svl in
        let rhs = CF.h_subst sst0 rhs in
        let rhs_b = CF.subst_b sst0 rhs_b in
        (* DD.info_pprint "  hp_rel found" pos; *)
        (*which pointers are defined and which arguments of data nodes are pointer*)
        let ( _,mix_lf,_,_,_) = CF.split_components (CF.Base lhs_b) in
        (* let (_,mix_rf,_,_,_) = CF.split_components (CF.Base rhs_b) in *)
        let leqs = (MCP.ptr_equations_without_null mix_lf) in
        let rls1,rls2  = List.split es.CF.es_rhs_eqset in
        let reqs = List.combine (CP.subst_var_list sst0 rls1) (CP.subst_var_list sst0 rls2)
          (* (MCP.ptr_equations_without_null mix_rf) *)  in
        let _ =
          DD.tinfo_pprint ">>>>>> infer_hp_rel <<<<<<" pos;
          DD.tinfo_pprint ("  es_heap: " ^ (Cprinter.string_of_h_formula es.CF.es_heap)) pos;
          DD.tinfo_pprint ("  es_history: " ^ (let pr=pr_list_ln Cprinter.string_of_h_formula in pr es.CF.es_history)) pos;
          DD.tinfo_pprint ("  lhs: " ^ (Cprinter.string_of_formula_base lhs_b)) pos;
          DD.tinfo_pprint ("  rhs: " ^ (Cprinter.string_of_formula_base rhs_b)) pos;
          DD.tinfo_pprint ("  unmatch: " ^ (Cprinter.string_of_h_formula rhs)) pos;
          DD.tinfo_pprint ("  classic: " ^ (string_of_bool !Globals.do_classic_frame_rule)) pos
        in
        let mis_nodes =  match rhs with
          | DataNode n -> [n.h_formula_data_node]
          | ViewNode n -> [n.h_formula_view_node]
          | HRel (_,eargs,_) -> CP.remove_dups_svl (List.concat (List.map CP.afv eargs))
          | _ -> report_error pos "Expect a node or a hrel"
                (* CF.get_ptr_from_data_w_hrel *)
        in
        (* let lhs_sel_vars = (CF.fv (CF.Base lhs_b)) in *)
        if (CP.intersect mis_nodes (List.fold_left SAU.close_def v_lhs leqs)) = [] then
          (
              let _ = Debug.tinfo_pprint ">>>>>> mismatch ptr is not a selective variable <<<<<<" pos in
              constant_checking prog rhs lhs_b rhs_b es
                  (* (false,es) *)
          )
        else
          (*********TODO: REMOVE HIS*****************)
          let no_es_history =  [] (* replacing es.CF.es_history *) in
          (* let no_es_history = es.CF.es_history in *)
          let his_ptrs = List.concat (List.map SAU.get_ptrs no_es_history) in
          (************** END HIS **************)
          let post_hps,prog_vars = get_prog_vars es.CF.es_infer_vars_sel_hp_rel rhs proving_kind#string_of in
          (********** BASIC INFO LHS, RHS **********)
          let l_hpargs = CF.get_HRels lhs_b.CF.formula_base_heap in
          let l_non_infer_hps = CP.diff_svl lhrs ivs in
          let r_hpargs = CF.get_HRels rhs in
          (**smart subst**)
          let lhs_b1, rhs_b1, subst_prog_vars = SAU.smart_subst lhs_b (formula_base_of_heap rhs pos) (l_hpargs@r_hpargs)
            (leqs@reqs) reqs [] (prog_vars@es.es_infer_vars)
          in
          let rhs = rhs_b1.CF.formula_base_heap in
          let ( _,mix_lf1,_,_,_) = CF.split_components (CF.Base lhs_b1) in
          let leqs1 = (MCP.ptr_equations_without_null mix_lf1) in
          let reqs1 = [] in
          (* let (_,mix_rf1,_,_,_) = CF.split_components (CF.Base rhs_b1) in *)
          (* let leqs1 = (MCP.ptr_equations_without_null mix_lf1) in *)
          (********** END BASIC INFO LHS, RHS **********)
          let is_found_mis, ls_unknown_ptrs,hds,hvs,lhras,rhras,eqNull,
            lselected_hpargs,rselected_hpargs,defined_hps, unk_svl,unk_pure,unk_map,new_lhs_hps =
            find_undefined_selective_pointers prog lhs_b1 mix_lf1 rhs rhs_rest
                (rhs_h_matched_set@his_ptrs) leqs1 reqs1 pos es.CF.es_infer_hp_unk_map post_hps subst_prog_vars in
          if not is_found_mis then
            let _ = Debug.info_pprint ">>>>>> mismatch ptr is not found (or inst) in the lhs <<<<<<" pos in
            (false, es, rhs, None)
          else
            let rhs_b1 = CF.formula_base_of_heap rhs pos in
            let lhs_new_hfs,lhs_new_hpargs = List.split new_lhs_hps in
            (*remove all non_infer_hps*)
            let lselected_hpargs1 = List.filter (fun (hp,_) -> not (CP.mem_svl hp l_non_infer_hps)) (lselected_hpargs) in
            let lselected_hpargs2 = lselected_hpargs1@lhs_new_hpargs in
            let defined_hps1 =  List.filter (fun (hp,_,_,_) -> not (CP.mem_svl hp l_non_infer_hps)) defined_hps in
            let n_lhs_b1 = match lhs_new_hfs with
               | [] -> lhs_b1
               | hf::rest -> CF.mkAnd_fb_hf lhs_b1 (List.fold_left(fun a c-> mkStarH a c pos ) hf rest) pos
            in
            let r_new_hfs,ass_lhs_b, m,rvhp_rels,hp_rel_list =
              generate_constraints prog es rhs n_lhs_b1 rhs_b1 defined_hps1
                  ls_unknown_ptrs unk_pure unk_svl no_es_history lselected_hpargs2 rselected_hpargs
                  hds hvs lhras lhrs rhras rhrs leqs1 reqs1 eqNull subst_prog_vars pos in
            (*update residue*)
            (*use leqs not leqs: since res is not substed*)
            let new_es, new_lhs = update_es prog es hds hvs ass_lhs_b rhs rhs_rest r_new_hfs defined_hps1 lselected_hpargs2
              rvhp_rels leqs m post_hps unk_map hp_rel_list pos in
            (true, new_es,new_lhs, None)
      end

let infer_collect_hp_rel i prog (es:entail_state) rhs rhs_rest (rhs_h_matched_set:CP.spec_var list) lhs_b rhs_b pos =
  let pr1 = Cprinter.string_of_formula_base in
  let pr4 = Cprinter.string_of_estate_infer_hp in
  let pr5 =  pr_quad string_of_bool pr4 Cprinter.string_of_h_formula (pr_option Cprinter.string_of_formula) in
  Debug.no_2_num i "infer_collect_hp_rel" pr1 pr1 pr5
( fun _ _ -> infer_collect_hp_rel_x prog es rhs rhs_rest rhs_h_matched_set lhs_b rhs_b pos) lhs_b rhs_b

let collect_classic_assumption prog lfb sel_hps infer_vars pos=
  let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lfb in
  let (_ ,mix_lf,_,_,_) = CF.split_components (CF.Base lfb) in
  let leqNulls = MCP.get_null_ptrs mix_lf in
  let leqs = (MCP.ptr_equations_without_null mix_lf) in
  let l_def_vs = leqNulls @ (List.map (fun hd -> hd.CF.h_formula_data_node) lhds)
    @ (List.map (fun hv -> hv.CF.h_formula_view_node) lhvs) in
  let l_def_vs = CP.remove_dups_svl (CF.find_close l_def_vs (leqs)) in
  let helper (hp,eargs,_)=(hp,List.concat (List.map CP.afv eargs)) in
  let ls_lhp_args = (List.map helper lhrs) in
  let _, defined_preds,rems_hpargs,link_hps =
    List.fold_left (fun (lfb1, r_defined_preds, r_rems, r_link_hps) hpargs ->
        let n_lfb,def_hps, rem_hps, ls_link_hps=
          SAU.find_well_defined_hp prog lhds lhvs []
              infer_vars [] hpargs (l_def_vs) lfb1 true pos
        in
        (n_lfb, r_defined_preds@def_hps, r_rems@rem_hps, r_link_hps@(snd (List.split ls_link_hps)))
    ) (lfb, [], [], []) ls_lhp_args
  in
  (* let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let _ = Debug.info_pprint (" rems_hpargs: " ^ (pr1 rems_hpargs)) no_pos in *)
  let truef = CF.mkTrue (CF.mkTrueFlow()) pos in
  let rem_defined= List.fold_left (fun ls (hp,args) ->
      if CP.mem_svl hp sel_hps then
        let hf = (CF.HRel (hp, List.map (fun x -> CP.mkVar x pos) args, pos)) in
        let new_defined = (hp, args, CF.formula_base_of_heap hf pos, truef) in
        (ls@[new_defined])
      else ls
  ) [] rems_hpargs in
  let defined_preds0 = defined_preds@rem_defined in
  let new_constrs =
    match defined_preds0 with
      | [] -> []
      | _ -> let defined_hprels = List.map (SAU.generate_hp_ass []) defined_preds0 in
        defined_hprels
  in
  (new_constrs, (List.map (fun (a, _, _,_) -> a) defined_preds0))

let infer_collect_hp_rel_classsic_x prog (es:entail_state) rhs pos =
  let _ = Debug.ninfo_pprint ("es_infer_vars_hp_rel: " ^ (!CP.print_svl es.es_infer_vars_hp_rel)) no_pos in
  let _ = Debug.ninfo_pprint ("es_infer_vars: " ^ (!CP.print_svl  es.es_infer_vars)) no_pos in
  let _ = Debug.ninfo_pprint ("es_infer_vars_sel_hp_rel: " ^ (!CP.print_svl  es.es_infer_vars_sel_hp_rel)) no_pos in
  if rhs<>HEmp || no_infer_hp_rel es then
    (false, es)
  else
    let lhs = es.CF.es_formula in
    let ivs = es.es_infer_vars_hp_rel in
    (*check whether LHS contains hp_rel*)
    let lhrs = CF.get_hp_rel_name_formula lhs in
    if CP.intersect ivs lhrs = [] then
      (false,es)
    else begin
      (*which pointers are defined and which arguments of data nodes are pointer*)
      let ( _,mix_lf,_,_,_) = CF.split_components lhs in
      let leqs = (MCP.ptr_equations_without_null mix_lf) in
      let _ =
        DD.tinfo_pprint ">>>>>> infer_hp_rel_classic <<<<<<" pos;
        DD.tinfo_pprint ("  es_heap: " ^ (Cprinter.string_of_h_formula es.CF.es_heap)) pos;
        DD.tinfo_pprint ("  lhs: " ^ (Cprinter.string_of_formula lhs)) pos;
        DD.tinfo_pprint ("  unmatch: " ^ (Cprinter.string_of_h_formula rhs)) pos;
        DD.tinfo_pprint ("  classic: " ^ (string_of_bool !Globals.do_classic_frame_rule)) pos
      in
      let l_hpargs = CF.get_HRels_f lhs in
      let l_non_infer_hps = CP.diff_svl lhrs ivs in
      (**smart subst**)
      let lhsb1 = SAU.smart_subst_lhs lhs l_hpargs leqs es.es_infer_vars in
      (**************COLLECT ASS*******************)
      let ls_ass, defined_hps = collect_classic_assumption prog lhsb1
        (es.es_infer_vars_hp_rel@es.es_infer_vars_sel_hp_rel) es.es_infer_vars pos in
      if ls_ass = [] then (false, es) else
      (**************REFINE RES*******************)
        let n_es_formula, _ = CF.drop_hrel_f es.es_formula defined_hps in
        let new_es = {es with (* CF. es_infer_vars_hp_rel = es.CF.es_infer_vars_hp_rel@rvhp_rels; *)
            CF.es_infer_hp_rel = es.CF.es_infer_hp_rel @ ls_ass;
            (* CF.es_infer_hp_unk_map = (es.CF.es_infer_hp_unk_map@unk_map); *)
            (* CF.es_infer_vars_sel_post_hp_rel = (es.CF.es_infer_vars_sel_post_hp_rel @ post_hps); *)
            CF.es_formula = n_es_formula}
        in
        DD.tinfo_pprint ("  new residue: " ^ (Cprinter.string_of_formula new_es.CF.es_formula)) pos;
        (true, new_es)
    end

let infer_collect_hp_rel_classsic i prog (es:entail_state) rhs pos =
  let pr1 = Cprinter.string_of_formula in
  let pr2 = Cprinter.string_of_h_formula in
  let pr3 = Cprinter.string_of_estate_infer_hp in
  let pr4 =  pr_pair string_of_bool pr3 in
  Debug.no_2_num i "infer_collect_hp_rel" pr1 pr2 pr4
( fun _ _ -> infer_collect_hp_rel_classsic_x prog es rhs pos) es.CF.es_formula rhs
(*=*****************************************************************=*)
         (*=**************INFER REL HP ASS*****************=*)
(*=*****************************************************************=*)

(******************************************************************************)

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

let print_spec spec file_name =
  let output_spec = file_name ^ ".spec" in
  let oc = open_out output_spec in
  Printf.fprintf oc "%s" spec;
  flush oc;
  close_out oc;;

let get_file_name full_file_name =
  try
    let pos = String.index full_file_name '.' in
    String.sub full_file_name 0 pos
  with _ -> report_error no_pos "Input file has a wrong format name"

let get_proc_name full_proc_name =
  try
    let pos = String.index full_proc_name '$' in
    String.sub full_proc_name 0 pos
  with _ -> report_error no_pos "Proc name has wrong format"

let rec string_of_elems elems string_of sep = match elems with 
  | [] -> ""
  | h::[] -> string_of h 
  | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)

let rec create_alias_tbl svl keep_vars aset = match svl with
  | [] -> []
  | [hd] -> 
    [hd::(List.filter (fun x -> not(List.mem x keep_vars)) (CP.EMapSV.find_equiv_all hd aset))]
  | hd::tl ->
    let tmp = create_alias_tbl [hd] keep_vars aset in
    let tl = List.filter (fun x -> not(List.mem x (List.hd tmp))) tl in
    tmp@(create_alias_tbl tl keep_vars aset)

(* Supposed fml to be Base _ *)
let filter_var_heap keep_vars fml =
  let _,pure,_,_,_ = CF.split_components fml in
  let als = MCP.ptr_equations_without_null pure in
(*  DD.info_hprint (add_str "ALS: " (pr_list (pr_pair !print_sv !print_sv))) als no_pos;*)
  let aset = CP.EMapSV.build_eset als in
  let alias_tbl = create_alias_tbl (keep_vars@CP.fv (MCP.pure_of_mix pure)) keep_vars aset in
  let subst_lst = 
    List.concat (List.map (fun vars -> if vars = [] then [] else 
      let hd = List.hd vars in 
      List.map (fun v -> (v,hd)) (List.tl vars)) alias_tbl) in
(*  DD.info_hprint (add_str "SUBS: " (pr_list (pr_pair !print_sv !print_sv))) subst_lst no_pos;*)
  let fml = CF.subst subst_lst fml in
  let heap,pure,_,_,_ = CF.split_components fml in
  let pure = CP.remove_redundant_constraints (MCP.pure_of_mix pure) in
(*  CF.normalize_combine_heap (CF.formula_of_pure_formula pure no_pos) heap*)
  (heap, pure)

let infer_shape input file_name view_node keep_vars proc_name = 
  domain_name := view_node;
  let fmls_orig = Parse_shape.parse_shape input in
  let keep_vars = keep_vars @ ["NULL"] in
  Debug.tinfo_hprint (add_str "Keep vars: " (pr_list (fun x -> x))) keep_vars no_pos;
  let keep_vars = List.map (fun s -> SpecVar (Named "GenNode", s, Unprimed)) keep_vars in
  let fmls = List.map (fun f -> filter_var_heap keep_vars f) fmls_orig in
(*  Debug.info_hprint (add_str "Inferred shape (original) " (pr_list !CF.print_formula)) fmls_orig no_pos;*)
(*  Debug.info_hprint (add_str "Inferred shape (filtered) " (pr_list !CF.print_formula)) fmls no_pos;*)
(*  print_newline ()*)
  let print_fun = fun (h,p) -> (!print_h_formula_for_spec h) ^ " &" ^ (!CP.print_formula p) in
  let pre = print_fun (List.hd fmls) in
  let post = string_of_elems (List.tl fmls) print_fun " ||" in
  let spec = proc_name ^ "\nrequires" ^ pre ^ "\nensures" ^ post ^ ";\n" in
  print_spec spec file_name;;

let get_shape_from_file view_node keep_vars proc_name = 
  let file_name = get_file_name Sys.argv.(1) in
  let input_c = file_name ^ ".c" in
(*  let _ = syscall ". ./../../predator/src/register-paths.sh" in*)
  let input_shape = file_name ^ ".shape" in
  let _ = syscall ("rm -f " ^ input_shape) in
  let _ = syscall ("gcc -fplugin=libsl.so -DPREDATOR " ^ input_c) in
  let input_str = syscall ("cat " ^ input_shape) in
  infer_shape input_str file_name view_node keep_vars proc_name

(*let get_cmd_from_file =*)
(*  let input_cmd = (get_file_name Sys.argv.(1)) ^ ".cmd" in*)
(*  let input_str = syscall ("cat " ^ input_cmd) in*)
(*  let res = Parse_cmd.parse_cmd input_str in*)
(*(*  print_endline ("SPEC" ^ ((pr_pair (fun x -> x) Cprinter.string_of_struc_formula) res));*)*)
(*  res*)

let get_spec_from_file prog = 
  let input_spec = (get_file_name Sys.argv.(1)) ^ ".spec" in
  let input_str = syscall ("cat " ^ input_spec) in
  let res = Parser.parse_specs_list input_str in
(*  print_endline ("SPEC" ^ (Iprinter.string_of_struc_formula res));*)
(*  let id,command = get_cmd_from_file in*)
  let id, command = !(IF.cmd) in
  let cmd = match command with
    | (true,_,Some view_node) -> 
      let proc = List.filter (fun x -> x.I.proc_name=id) prog.I.prog_proc_decls in
      let keep_vars = 
        if List.length proc != 1 then report_error no_pos ("Error in get_spec_from_file " ^ input_spec)
        else 
          List.map (fun x -> x.I.param_name) (List.hd proc).I.proc_args
      in
      let _ = get_shape_from_file view_node keep_vars id in
      IF.mkETrue top_flow no_pos
    | (false,Some cmd,_) -> cmd
    | _ -> report_error no_pos "No command"
  in
  let res = List.map (fun (id1,spec) -> 
    if id1=id then (id1,IF.merge_cmd cmd spec) else (id1,spec)) res in
  res

(******************************************************************************)

(*let infer_empty_rhs estate lhs_p rhs_p pos =*)
(*  estate*)

(* let infer_empty_rhs_old estate lhs_p rhs_p pos = *)
(*   if no_infer estate then estate *)
(*   else *)
(*     let _ = DD.devel_pprint ("\n inferring_empty_rhs:"^(!print_formula estate.es_formula)^ "\n\n")  pos in *)
(*     let rec filter_var f vars = match f with *)
(*       | CP.Or (f1,f2,l,p) -> CP.Or (filter_var f1 vars, filter_var f2 vars, l, p) *)
(*       | _ -> CP.filter_var f vars *)
(*     in *)
(*     let infer_pure = MCP.pure_of_mix rhs_p in *)
(*     let infer_pure = if CP.isConstTrue infer_pure then infer_pure *)
(*     else CP.mkAnd (MCP.pure_of_mix rhs_p) (MCP.pure_of_mix lhs_p) pos *)
(*     in *)
(*     (\*        print_endline ("PURE: " ^ Cprinter.string_of_pure_formula infer_pure);*\) *)
(*     let infer_pure = Omega.simplify (filter_var infer_pure estate.es_infer_vars) in *)
(*     let pure_part2 = Omega.simplify (List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos) *)
(*         (estate.es_infer_pures @ [MCP.pure_of_mix rhs_p])) in *)
(*     (\*        print_endline ("PURE2: " ^ Cprinter.string_of_pure_formula infer_pure);*\) *)
(*     let infer_pure = if Omega.is_sat pure_part2 "0" = false then [CP.mkFalse pos] else [infer_pure] in *)
(*       {estate with es_infer_heap = []; es_infer_pure = infer_pure; *)
(*           es_infer_pures = estate.es_infer_pures @ [(MCP.pure_of_mix rhs_p)]} *)

(*let infer_empty_rhs2 estate lhs_xpure rhs_p pos =*)
(*  estate*)

(* let infer_empty_rhs2_old estate lhs_xpure rhs_p pos = *)
(*   if no_infer estate then estate *)
(*   else *)
(*     let _ = DD.devel_pprint ("\n inferring_empty_rhs2:"^(!print_formula estate.es_formula)^ "\n\n")  pos in *)
(*     (\* let lhs_xpure,_,_,_ = xpure prog estate.es_formula in *\) *)
(*     let pure_part_aux = Omega.is_sat (CP.mkAnd (MCP.pure_of_mix lhs_xpure) (MCP.pure_of_mix rhs_p) pos) "0" in *)
(*     let rec filter_var_aux f vars = match f with *)
(*       | CP.Or (f1,f2,l,p) -> CP.Or (filter_var_aux f1 vars, filter_var_aux f2 vars, l, p) *)
(*       | _ -> CP.filter_var f vars *)
(*     in *)
(*     let filter_var f vars =  *)
(*       if CP.isConstTrue (Omega.simplify f) then CP.mkTrue pos  *)
(*       else *)
(*         let res = filter_var_aux f vars in *)
(*         if CP.isConstTrue (Omega.simplify res) then CP.mkFalse pos *)
(*         else res *)
(*     in *)
(*     let invs = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos) estate.es_infer_invs in *)
(*     let pure_part =  *)
(*       if pure_part_aux = false then *)
(*         let mkNot purefml =  *)
(*           let conjs = CP.split_conjunctions purefml in *)
(*           let conjs = List.map (fun c -> CP.mkNot_s c) conjs in *)
(*           List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos) conjs *)
(*         in *)
(*         let lhs_pure = CP.mkAnd (mkNot(Omega.simplify  *)
(*             (filter_var (MCP.pure_of_mix lhs_xpure) estate.es_infer_vars))) invs pos in *)
(*         (\*print_endline ("PURE2: " ^ Cprinter.string_of_pure_formula lhs_pure);*\) *)
(*         CP.mkAnd lhs_pure (MCP.pure_of_mix rhs_p) pos *)
(*       else Omega.simplify (CP.mkAnd (CP.mkAnd (MCP.pure_of_mix lhs_xpure) (MCP.pure_of_mix rhs_p) pos) invs pos) *)
(*     in *)
(*     let pure_part = filter_var (Omega.simplify pure_part) estate.es_infer_vars in *)
(*     (\*        print_endline ("PURE: " ^ Cprinter.string_of_mix_formula rhs_p);*\) *)
(*     let pure_part = Omega.simplify pure_part in *)
(*     let pure_part2 = Omega.simplify (CP.mkAnd pure_part  *)
(*         (List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos)  *)
(*             (estate.es_infer_pures @ [MCP.pure_of_mix rhs_p])) pos) in *)
(*     (\*        print_endline ("PURE1: " ^ Cprinter.string_of_pure_formula pure_part);*\) *)
(*     (\*        print_endline ("PURE2: " ^ Cprinter.string_of_pure_formula pure_part2);*\) *)
(*     let pure_part = if (CP.isConstTrue pure_part & pure_part_aux = false)  *)
(*       || Omega.is_sat pure_part2 "0" = false then [CP.mkFalse pos] else [pure_part] in *)
(*     {estate with es_infer_heap = []; es_infer_pure = pure_part; *)
(*         es_infer_pures = estate.es_infer_pures @ [(MCP.pure_of_mix rhs_p)]} *)

(* Calculate the invariant relating to unfolding *)
(*let infer_for_unfold prog estate lhs_node pos =
  if no_infer estate then estate
  else
(*    let _ = DD.devel_pprint ("\n inferring_for_unfold:"^(!print_formula estate.CF.es_formula)^ "\n\n")  pos in*)
    let inv = match lhs_node with
      | ViewNode ({h_formula_view_name = c}) ->
        let vdef = Cast.look_up_view_def pos prog.Cast.prog_view_decls c in
        let i = MCP.pure_of_mix (fst vdef.Cast.view_user_inv) in
        if List.mem i estate.es_infer_invs then estate.es_infer_invs
        else estate.es_infer_invs @ [i]
      | _ -> estate.es_infer_invs
    in {estate with es_infer_invs = inv} *)


(* Calculate the invariant relating to unfolding *)
(*let infer_for_unfold prog estate lhs_node pos =
  let pr es =  pr_list !CP.print_formula es.es_infer_invs in
  let pr2 = !print_h_formula in
  Debug.no_2 "infer_for_unfold" 
      (add_str "es_infer_inv (orig) " pr) 
      (add_str "lhs_node " pr2) 
      (add_str "es_infer_inv (new) " pr)
      (fun _ _ -> infer_for_unfold prog estate lhs_node pos) estate lhs_node*)


(* let infer_for_unfold_old prog estate lhs_node pos = *)
(*   if no_infer estate then estate *)
(*   else *)
(*     let _ = DD.devel_pprint ("\n inferring_for_unfold:"^(!print_formula estate.es_formula)^ "\n\n")  pos in *)
(*     let inv = matchcntha lhs_node with *)
(*       | ViewNode ({h_formula_view_name = c}) -> *)
(*             let vdef = Cast.look_up_view_def pos prog.Cast.prog_view_decls c in *)
(*             let i = MCP.pure_of_mix (fst vdef.Cast.view_user_inv) in *)
(*             if List.mem i estate.es_infer_invs then estate.es_infer_invs *)
(*             else estate.es_infer_invs @ [i] *)
(*       | _ -> estate.es_infer_invs *)
(*     in {estate with es_infer_invs = inv}  *)

(* type: ((CP.spec_var * h_formula) * CP.spec_var list) list -> *)
(*   CP.formula list -> list_context -> list_context option *)


let add_infer_hp_contr_to_list_context h_arg_map cp (l:list_context) : list_context option= 
	 (* let new_cp = List.concat (List.map CP.split_conjunctions cp) in *)
	 let new_cp = List.map CP.arith_simplify_new cp in
	 (*let _ = print_string ("\n new_cp: "^(!CP.print_formula (List.hd new_cp))^"\n") in*)
	 try
		 let new_rels = List.map (fun c->
			let fv = CP.fv c in
			let new_hd = List.filter (fun (_,vl)-> Gen.BList.overlap_eq CP.eq_spec_var fv vl) h_arg_map in
			(*let _ = print_string ("\n matching rels: "^(string_of_int (List.length new_hd))^"\n") in*)
			(*let _ = print_string ("\n new_cp fv: "^(!print_svl fv)^"\n") in*)
			match new_hd with
			 | [((h,hf),h_args)] -> 
				if (Gen.BList.subset_eq CP.eq_spec_var fv h_args (*(List.concat (snd (List.split new_hd)))*)) then
                                  (*LOC changed here. may be wrong*)
				mkHprel (CP.HPRelDefn (h, List.hd h_args, List.tl h_args )) h_args [] []  (formula_of_heap hf no_pos) (formula_of_pure_N c no_pos)  				
				else raise Not_found
			| _ -> raise Not_found ) new_cp in
                 let _ = rel_ass_stk # push_list (new_rels) in
                 let _ = Log.current_hprel_ass_stk # push_list (new_rels) in
		 let scc_f es = Ctx {es with es_infer_hp_rel = new_rels@es.es_infer_hp_rel;} in
		 Some (transform_list_context (scc_f, (fun a -> a)) l)
	 with Not_found -> None

let add_infer_hp_contr_to_list_context h_arg_map cp (l:list_context) : list_context option =
  let pr1 = pr_list (pr_pair (pr_pair !print_sv pr_none) !print_svl) in 
  let pr2 = pr_list !CP.print_formula in
  let pr3 = !print_list_context in
  Debug.no_3 "add_infer_hp_contr_to_list_context" pr1 pr2 pr3 (pr_option pr3)
      add_infer_hp_contr_to_list_context h_arg_map cp l
