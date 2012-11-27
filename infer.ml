open Globals
module DD = Debug
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
  let ra = MCP.pure_ptr_equations lhs in
  let (subs,rest) = CP.simplify_subs ra vars [] in
  let nsubs = CP.norm_subs (rest@subs) in
  let asubs = rest@nsubs in	  
  let n_rhs = (CP.subst asubs rhs) in
  let lhs = (CP.subst asubs lhs) in
  let lhs = simplify_conjs lhs in
  let n_lhs = CP.filter_ante lhs n_rhs in
  (c,n_lhs,n_rhs)

(************************************************)

let rel_ass_stk : hprel Gen.stack_pr = new Gen.stack_pr 
  Cprinter.string_of_hprel_short (==)

let no_infer estate = (estate.es_infer_vars == [])

let no_infer_rel estate = (estate.es_infer_vars_rel == [])

let no_infer_hp_rel estate = (estate.es_infer_vars_hp_rel == [])

let no_infer_all estate = (estate.es_infer_vars == [] && estate.es_infer_vars_rel == [])
  
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
              (* TODO : how to handle multiple rel on LHS *)
              if (List.length vs_rel)>1 then 
                 (None,[]) 
              else
                let rel_ass = infer_lhs_contra p_thus lhs_xpure vs_lhs pos "relational assumption" in
                begin
                  match rel_ass with
                  | None -> (None, [])
                  | Some neg_lhs ->
                    if (CP.fv neg_lhs == []) then (None,[])
                    else 
                      let new_estate = CF.false_es_with_orig_ante estate estate.es_formula pos in
                      (Some (new_estate,CP.mkTrue no_pos), [ (RelAssume vs_rel,f,neg_lhs)] )
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

let infer_lhs_contra_estate e f pos msg =
  let pr0 = !print_entail_state_short in
  let pr = !print_mix_formula in
  let pr_res = pr_pair (pr_option (pr_pair pr0 !CP.print_formula)) (fun l -> (string_of_int (List.length l))) in
  Debug.no_2 "infer_lhs_contra_estate" pr0 pr pr_res (fun _ _ -> infer_lhs_contra_estate e f pos msg) e f

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

(* let infer_h prog estate conseq lhs_b rhs_b lhs_rels*)

(* lhs_rel denotes rel on LHS where rel assumption be inferred *)
let infer_pure_m estate lhs_rels lhs_xpure(* _orig *) (lhs_xpure0:MCP.mix_formula) lhs_wo_heap (rhs_xpure_orig:MCP.mix_formula) pos =
  if (no_infer estate) && (lhs_rels==None) then (None,None,[])
  else
    if not (TP.is_sat_raw rhs_xpure_orig) then 
      (* (DD.devel_pprint "Cannot infer a precondition: RHS contradiction" pos; *)
      (* (None,None,[])) *)
      let p, rel_ass = infer_lhs_contra_estate estate lhs_xpure0 pos "rhs contradiction" in
      (p,None,[])
    else
      (* let lhs_xpure = MCP.pure_of_mix lhs_xpure_orig in *)
      (* let rhs_vars = CP.fv rhs_xpure in *)
      (* below will help greatly reduce the redundant information inferred from state *)
      (* let lhs_xpure = CP.filter_ante lhs_xpure rhs_xpure in *)
      let rhs_xpure = MCP.pure_of_mix rhs_xpure_orig in 
      let _ = DD.trace_hprint (add_str "lhs(orig): " !CP.print_formula) lhs_xpure pos in
      let _ = DD.trace_hprint (add_str "lhs0(orig): " !print_mix_formula) lhs_xpure0 pos in
      let _ = DD.trace_hprint (add_str "rhs(orig): " !CP.print_formula) rhs_xpure pos in
      let lhs_xpure = CP.filter_ante lhs_xpure rhs_xpure in
      let _ = DD.trace_hprint (add_str "lhs (after filter_ante): " !CP.print_formula) lhs_xpure pos in
      let fml = CP.mkAnd lhs_xpure rhs_xpure pos in
      let fml = CP.drop_rel_formula fml in
      let iv_orig = estate.es_infer_vars in
      (* let iv_lhs_rel = match lhs_rels with *)
      (*   | None -> [] *)
      (*   | Some f -> List.filter (fun x -> not(is_rel_var x)) (CP.fv f) in *)
      (* Debug.trace_hprint (add_str "iv_orig" !CP.print_svl) iv_orig no_pos; *)
      (* Debug.trace_hprint (add_str "iv_lhs_rel" !CP.print_svl) iv_lhs_rel no_pos; *)
      let iv = iv_orig(* @iv_lhs_rel *) in
      let _ = DD.trace_hprint (add_str "fml: " !CP.print_formula) fml pos in
      let check_sat = TP.is_sat_raw (MCP.mix_of_pure fml) in
      if not(check_sat) then
        (DD.devel_pprint "LHS-RHS contradiction" pos;
        (* let lhs_xpure0 = MCP.pure_of_mix lhs_xpure0 in *)
        let _ = DD.trace_hprint (add_str "lhs0: " !print_mix_formula) lhs_xpure0 pos in
        let _ = DD.trace_hprint (add_str "rhs: " !CP.print_formula) rhs_xpure pos in
        (* let lhs_xpure0 = CP.filter_ante lhs_xpure0 rhs_xpure in *)
        (* let _ = DD.trace_hprint (add_str "lhs0 (after filter_ante): " !CP.print_formula) lhs_xpure0 pos in *)
        let p, rel_ass = infer_lhs_contra_estate estate lhs_xpure0 pos "ante contradict with conseq" in
        (p,None,[]))
      else
      (*let invariants = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos) estate.es_infer_invs in*)
      (* if check_sat then *)
      (*      let new_p = simplify fml iv in                            *)
      (*      let new_p = simplify (CP.mkAnd new_p invariants pos) iv in*)
      (*      if CP.isConstTrue new_p then None                         *)
      (*      else                                                      *)
      let lhs_wo_heap = CP.drop_rel_formula (MCP.pure_of_mix lhs_wo_heap) in
      let lhs_wo_ptr_eqs = MCP.remove_ptr_equations lhs_wo_heap false in
      let vars_lhs = fv lhs_wo_ptr_eqs in (* var on lhs *)
      let vars_rhs = fv (MCP.remove_ptr_equations rhs_xpure false) in (* var on rhs *)
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
      let quan_var_new = quan_var (*@vars_overlap*) in
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
          let lhs_xpure = Cpure.add_ann_constraints imm_vrs lhs_xpure in
          let _ = DD.trace_hprint (add_str "lhs_xpure(w ann): " !CP.print_formula) lhs_xpure pos  in
          let new_p = TP.simplify_raw (CP.mkForall quan_var_new 
            (CP.mkOr (CP.mkNot_s lhs_xpure) rhs_xpure None pos) None pos) in
          let new_p = if not(isConstFalse new_p) then new_p else
          (* Use quan_var instead *)
            TP.simplify_raw (CP.mkForall quan_var 
            (CP.mkOr (CP.mkNot_s lhs_xpure) rhs_xpure None pos) None pos) in
(*          let fml2 = TP.simplify_raw (CP.mkExists quan_var_new fml None no_pos) in*)
          let new_p_for_assume = new_p in
          let _ = DD.devel_hprint (add_str "new_p_assume: " !CP.print_formula) new_p pos in
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
      (* abstract common terms from disj into conjunctive form *)
      if (CP.isConstTrue new_p || CP.isConstFalse new_p) then 
        begin
          if (lhs_rels==None || not(CP.isConstFalse new_p_ass)) then
            begin
                  DD.devel_pprint ">>>>>> infer_pure_m <<<<<<" pos;
                  DD.devel_pprint "Did not manage to infer a useful precondition" pos;
                  DD.devel_hprint (add_str "LHS : " !CP.print_formula) lhs_xpure pos;               
                  DD.devel_hprint (add_str "RHS : " !CP.print_formula) rhs_xpure pos;
                  (* DD.devel_hprint (add_str "new pure: " !CP.print_formula) new_p pos; *)
                  DD.devel_hprint (add_str "new pure: " !CP.print_formula) new_p pos;
                  (None,None,[])
            end
          else match lhs_rels with
            | Some f ->
                  DD.devel_pprint ">>>>>> infer_pure_m <<<<<<" pos;
                  DD.devel_pprint "Add relational assumption" pos;
                  DD.devel_hprint (add_str "new pure: " !CP.print_formula) new_p pos;
                  DD.devel_hprint (add_str "new pure ass: " !CP.print_formula) new_p_ass pos;
                  let (vs_rel,vs_lhs) = List.partition CP.is_rel_var (CP.fv f) in
                  let n_rhs = rhs_xpure in
                  let n_lhs = lhs_xpure in
                  (* let vars = stk_vars # get_stk in *)
			            (* let (_,n_lhs,n_rhs) = simp_lhs_rhs vars (0,lhs_xpure,rhs_xpure) in *)
                  (* TODO : how to handle multiple rel on LHS *)
                  if ((List.length vs_rel)>1) then 
                    let vars = stk_vars # get_stk in
			              let (_,n_lhs,n_rhs) = simp_lhs_rhs vars (0,lhs_xpure,rhs_xpure) in
                    (* (None,None,[]) *)
                    (None,None,[ (RelAssume vs_rel,n_lhs,n_rhs) ])
                  else
                    begin
                  let n_lhs2 = CP.drop_rel_formula n_lhs in
(*                  let n_lhs3 = filter_ante n_lhs2 n_rhs in*)
                  let n_lhs3 = filter_var n_lhs2 vs_lhs in
                  let args = CP.fv n_lhs3 in (* var on lhs *)
                  (* Update vars_overlap with vars_lhs *)
                  let total_sub_flag = List.for_all (fun r ->
                    let alias = r::(CP.EMapSV.find_equiv_all r lhs_aset) in
                    CP.intersect alias vs_lhs != []) vars_rhs in
                  let total_sub_flag = if (CP.diff_svl vs_lhs vars_rhs == []) then false else total_sub_flag in
                  Debug.trace_hprint (add_str "total_sub_flag" string_of_bool) total_sub_flag no_pos;
                  let vars_rhs = List.concat (List.map (fun r -> r::(CP.EMapSV.find_equiv_all r lhs_aset)) vars_rhs) in
                  let vars_overlap =  if total_sub_flag then (CP.intersect_svl vars_lhs vars_rhs) else [] in
                  Debug.trace_hprint (add_str "vars overlap" !CP.print_svl) vars_overlap no_pos;
                  let quan_var = (CP.diff_svl args vs_lhs) @ vars_overlap in
                  let new_p = TP.simplify_raw (CP.mkForall quan_var 
                      (CP.mkOr (CP.mkNot_s n_lhs3) n_rhs None pos) None pos) in
                  let trace = Debug.tinfo_hprint in
                  trace (add_str "f (rel)" !print_formula) f no_pos;
                  trace (add_str "vs_rel" !print_svl) vs_rel no_pos;
                  trace (add_str "vs_lhs" !print_svl) vs_lhs no_pos;
                  trace (add_str "quan" !print_svl) quan_var no_pos;
                  trace (add_str "lhs (after drop_compl)" !print_formula) n_lhs2 no_pos;
                  trace (add_str "lhs (after filter)" !print_formula) n_lhs3 no_pos;
                  trace (add_str "rhs" !print_formula) n_rhs no_pos;
                  trace (add_str "new_p (rel_ass)" !print_formula) new_p no_pos;
                  if (CP.fv new_p == []) then (None,None,[])
                  else (None,None, [ (RelAssume vs_rel,f,new_p)] )
                  end
            | None -> (None,None,[])
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


let infer_pure_m estate lhs_xpure_orig lhs_xpure0 lhs_wo_heap rhs_xpure_mix pos =
  if (no_infer estate) && (no_infer_rel estate) then 
    (None,None,[])
  else 
    let rhs_xpure = MCP.pure_of_mix rhs_xpure_mix in
(*    let lhs_xpure0 = MCP.pure_of_mix lhs_xpure0 in*)
    let lhs_xpure_orig = MCP.pure_of_mix lhs_xpure_orig in
    let cl = CP.filter_ante lhs_xpure_orig rhs_xpure in
    let cl = CP.split_conjunctions cl in
    let ivs = estate.es_infer_vars_rel in
    let (lhs_rel, lhs_wo_rel) = 
      List.partition (fun d -> (CP.get_RelForm d) != [] ) cl in
    let lhs_rel = 
      List.filter (fun d -> (CP.intersect (CP.fv d) ivs) != [] ) lhs_rel in
    let lhs_rels,xp = match lhs_rel with 
      | [] -> None, join_conjunctions lhs_wo_rel
      | _ -> Debug.trace_hprint (add_str "lhs_rels" (pr_list !CP.print_formula)) lhs_rel no_pos;
            let v = join_conjunctions lhs_rel in
            Some (join_conjunctions lhs_rel), join_conjunctions (v::lhs_wo_rel)
    in
    Debug.tinfo_hprint (add_str "lhs_xpure_orig" !CP.print_formula) lhs_xpure_orig no_pos;
    Debug.tinfo_hprint (add_str "lhs_xpure0" !print_mix_formula) lhs_xpure0 no_pos;
    Debug.tinfo_hprint (add_str "lhs_rels" (pr_opt !CP.print_formula)) lhs_rels no_pos;
    Debug.tinfo_hprint (add_str "xp" !CP.print_formula) xp no_pos;
    infer_pure_m estate lhs_rels xp lhs_xpure0 lhs_wo_heap rhs_xpure_mix pos

let infer_pure_m estate lhs_xpure lhs_xpure0 lhs_wo_heap rhs_xpure pos =
  (* let _ = print_endline "WN : inside infer_pure_m" in *)
  let pr1 = !print_mix_formula in 
  let pr2 = !print_entail_state_short in 
  let pr_p = !CP.print_formula in
  let pr_res = pr_triple (pr_option (pr_pair pr2 !print_pure_f)) (pr_option pr_p) (fun l -> (string_of_int (List.length l))) in
  let pr0 es = pr_pair pr2 !CP.print_svl (es,es.es_infer_vars) in
      Debug.no_4 "infer_pure_m" 
          (add_str "estate " pr0) 
          (add_str "lhs xpure " pr1) 
          (add_str "lhs xpure0 " pr1)
          (add_str "rhs xpure " pr1)
          (add_str "(new es,inf pure,rel_ass) " pr_res)
      (fun _ _ _ _ -> infer_pure_m estate lhs_xpure lhs_xpure0 lhs_wo_heap rhs_xpure pos) estate lhs_xpure lhs_xpure0 rhs_xpure   

let remove_contra_disjs f1s f2 =
  let helper c1 c2 = 
    let conjs1 = CP.list_of_conjs c1 in
    let conjs2 = CP.list_of_conjs c2 in
    (Gen.BList.intersect_eq CP.equalFormula conjs1 conjs2) != []
  in 
  let new_f1s = List.filter (fun f -> helper f f2) f1s in
  match new_f1s with
    | [] -> f1s
    | [hd] -> [hd]
    | ls -> f1s
  

let lhs_simplifier lhs_h lhs_p =
  let disjs = CP.list_of_disjs lhs_h in
  let disjs = remove_contra_disjs disjs lhs_p in
  snd (trans_dnf (CP.mkAnd (disj_of_list disjs no_pos) lhs_p no_pos))

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
    (TP.simplify_raw_w_rel (mkAnd lhs_h lhs_p no_pos))

let lhs_simplifier_tp lhs_h lhs_p =
  let pr = !CP.print_formula in
    Debug.no_2 "lhs_simplifier_tp" pr pr pr lhs_simplifier_tp lhs_h lhs_p

(* to filter relevant LHS term for selected relation rel *)
(* requires simplify and should preserve relation and != *)
let rel_filter_assumption is_sat lhs rel =
  (* let (lhs,rel) = CP.assumption_filter_aggressive_incomplete  lhs rel in *)
  let (lhs,rel) = CP.assumption_filter_aggressive is_sat lhs rel in
  (lhs,rel)

(* let rel_filter_assumption lhs rel = *)
(*   let pr = CP.print_formula in *)
(*   Debug.no_2 "rel_filter_assumption" pr pr (fun (r,_) -> pr r) rel_filter_assumption lhs rel  *)

let delete_present_in i_pure compared_pure_list =
  let i_pure_list = CP.split_conjunctions i_pure in
  let i_pure_list = List.filter (fun p -> not (present_in compared_pure_list p)) i_pure_list in
  CP.join_conjunctions i_pure_list

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

(* Assume fml is conjs *)
(*let filter_rank fml lhs_cond =
  let (rank, others) = List.partition (fun p -> CP.is_Rank_Dec p || CP.is_Rank_Const p) (CP.split_conjunctions fml) in
  let (rank_dec, rank_const) = List.partition (fun p -> CP.is_Rank_Dec p) rank in
  let rank_dec = List.map (fun r -> check_rank_dec r lhs_cond) rank_dec in
  let rank_const = List.map (fun r -> check_rank_const r lhs_cond) rank_const in
  CP.join_conjunctions (rank_dec@rank_const@others) *)

let infer_collect_rel is_sat estate xpure_lhs_h1 (* lhs_h *) lhs_p_orig (* lhs_b *) rhs_p pos =
  (* TODO : need to handle pure_branches in future ? *)
  if no_infer_rel estate then (estate,lhs_p_orig,rhs_p) 
  else 
    let ivs = estate.es_infer_vars_rel in
    let rhs_p_n = MCP.pure_of_mix rhs_p in
    (* Eliminate dijs in rhs which cannot be implied by lhs and do not contain relations *)
    (* Suppose rhs_p_n is in DNF *)
    (* Need to assure that later *)
(*    let rhs_disjs = CP.list_of_disjs rhs_p_n in
    let (rhs_disjs_rel, rhs_disjs_wo_rel) = 
      List.partition (fun d -> CP.get_RelForm d != [] || CP.get_Rank d != []) rhs_disjs in
    let lhs_cond = MCP.pure_of_mix lhs_p_orig in
    let rhs_disjs_wo_rel_new, other_disjs = List.partition (fun d -> TP.imply_raw lhs_cond d) rhs_disjs_wo_rel in
    let other_disjs = List.filter (fun d -> TP.is_sat_raw (CP.mkAnd lhs_cond d no_pos)) other_disjs in
    (* DD.devel_hprint (add_str "LHS pure" !CP.print_formula) (MCP.pure_of_mix lhs_p_orig) pos; *)
    (* DD.devel_hprint (add_str "RHS Disj List" (pr_list !CP.print_formula)) rhs_disjs pos; *)
    let pairs = List.map (fun pure ->
      let rhs_ls = CP.split_conjunctions pure in
      let rels, others = List.partition (fun p -> CP.is_rel_in_vars ivs p || CP.has_func p) rhs_ls in
      let rels = if List.exists (fun p -> CP.is_Rank_Const p) rels then [CP.conj_of_list rels no_pos] else rels in
      rels, others)
      (rhs_disjs_rel @ rhs_disjs_wo_rel_new) in*)
    let pairs = List.map (fun pure ->
      let rhs_ls = CP.split_conjunctions pure in
      let rels, others = List.partition (fun p -> CP.is_rel_in_vars ivs p || CP.has_func p) rhs_ls in
      rels, others) (CP.list_of_disjs rhs_p_n) in
    let rel_rhs_ls, other_rhs_ls = List.split pairs in
    let rel_rhs = List.concat rel_rhs_ls in
    if rel_rhs==[] then (
      DD.devel_pprint ">>>>>> infer_collect_rel <<<<<<" pos; 
      DD.devel_pprint "no relation in rhs" pos; 
      (estate,lhs_p_orig,rhs_p)
    (* DD.devel_hprint (add_str "RHS pure" !CP.print_formula) rhs_p_n_new pos; *)
    (* TODO : need to check if relation occurs in both lhs & rhs of original entailment *)
    (* Check if it is related to being unable to fold rhs_heap *)
    (*      if !unable_to_fold_rhs_heap = false then
            (estate,lhs_p_orig,rhs_p,rhs_p_br)
	    else (
            unable_to_fold_rhs_heap := false;
            let lhs_xpure = MCP.merge_mems xpure_lhs_h1 lhs_p_orig true in
            let evars = estate.es_evars@estate.es_gen_expl_vars@estate.es_ivars in
            let _, new_rhs_p = heap_entail_build_mix_formula_check evars lhs_p_orig rhs_p pos in
            let lhs_p = MCP.pure_of_mix lhs_p_orig in
            let rel_lhs = CP.get_RelForm lhs_p in
            let infer_vars = CP.remove_dups_svl (List.concat (List.map CP.get_rel_args rel_lhs)) in
            let new_estate = {estate with es_infer_vars = infer_vars} in
            let inferred_pure = infer_pure_m new_estate lhs_xpure lhs_xpure lhs_xpure new_rhs_p pos in
            let (estate, lhs_p) = begin
            match inferred_pure with
    (* TODO : how to handle rel_ass ?? *)
            | (None, Some p, rel_ass) ->
            let vl =  estate.es_infer_vars in
            if CP.subset (CP.fv p) vl then (estate, lhs_p)
            else
            (DD.devel_pprint ">>>>>> infer_collect_rel <<<<<<" pos;
            DD.devel_pprint "unable to fold rhs_heap because of relations" pos;
            DD.trace_hprint (add_str "infer pure" !CP.print_formula) p no_pos;
            DD.trace_hprint (add_str "ivars" !CP.print_svl) vl no_pos;
            ({estate with es_assumed_pure = estate.es_assumed_pure @ [p]}, CP.mkAnd lhs_p p pos))
            | _ -> (estate, lhs_p)
            end
            in
            (estate,MCP.mix_of_pure lhs_p,rhs_p,rhs_p_br)
	    )*)
    )
    else 
      (* TODO: Check if inferred rel can imply es_assumed_pure in the end *)

      (*      let lhs_orig = MCP.pure_of_mix lhs_p_orig in
	      DD.devel_hprint (add_str "Assumed pure list:" (pr_list !CP.print_formula)) estate.es_assumed_pure pos;
	      let assumed_pure_list = List.concat (List.map CP.split_conjunctions estate.es_assumed_pure) in
	      let lhs_orig = delete_present_in lhs_orig assumed_pure_list in
	      let lhs_p_orig = MCP.mix_of_pure lhs_orig in
	      let h, p, fl, b, t = split_components estate.es_formula in
	      let p = delete_present_in (MCP.pure_of_mix p) assumed_pure_list in
	      let fml = mkBase h (MCP.mix_of_pure p) t fl b pos in
	      let estate = {estate with es_formula = fml} in*)
      let lhs_p = MCP.pure_of_mix lhs_p_orig in
      let (lhs_p_memo,subs,bvars) = CP.memoise_rel_formula ivs lhs_p in
      (* Begin: To keep vars of rel_form in lhs *)
      let _,rel_lhs = List.split subs in
      let rel_vars = List.concat (List.map CP.fv rel_lhs) in
      (* End  : To keep vars of rel_form in lhs *)

      (*let pr = !CP.print_formula_br in*)
      (* let _ = print_endline (pr rhs_p_br) in *)
      (*let ranks = List.filter CP.has_func rel_rhs in*)
(*      let rhs_p_2 = CP.disj_of_list ((List.map (fun other_rhs -> CP.join_conjunctions other_rhs) other_rhs_ls)@other_disjs) no_pos in*)
      let rhs_p_2 = CP.disj_of_list ((List.map (fun other_rhs -> CP.join_conjunctions other_rhs) other_rhs_ls)(*@other_disjs*)) no_pos in
      let rhs_p_new = MCP.mix_of_pure rhs_p_2 in

      (* Eliminate relations whose recursive calls are not defined *)
      (* e.g. A(x) <- A(t) && other_constraints, *)
      (* where other_constraints are not related to variable t *)
      let lhs_rec_vars = CP.fv lhs_p_memo in
      if CP.intersect lhs_rec_vars rel_vars = [] && rel_lhs != [] then (
        DD.devel_pprint ">>>>>> infer_collect_rel <<<<<<" pos;
        DD.devel_pprint ">>>>>> no recursive def <<<<<<" pos; 
        (estate,lhs_p_orig,rhs_p_new))
      else
        let lhs_h = MCP.pure_of_mix xpure_lhs_h1 in
        (* let lhs = lhs_simplifier lhs_h lhs_p_memo in *)
        DD.trace_hprint (add_str "lhs_p:" (!CP.print_formula)) lhs_p pos;
        DD.trace_hprint (add_str "lhs_p_memo:" (!CP.print_formula)) lhs_p_memo pos;
        DD.trace_hprint (add_str "lhs_h (xpure_lhs_h1):" (!CP.print_formula)) lhs_h pos;

        let lhs = lhs_simplifier_tp lhs_h lhs_p_memo in
        DD.trace_hprint (add_str "lhs (after lhs_simplifier):" (!CP.print_formula)) lhs pos;
        let lhs_2 = CP.restore_memo_formula subs bvars lhs in
        DD.trace_hprint (add_str "lhs_2 (b4 filter ass):" (!CP.print_formula)) lhs_2 pos;
        (* TODO: Need a faster filter_assumption *)
        let is_bag_cnt = TP.is_bag_constraint lhs in
        let filter_ass lhs rhs = 
          let is_sat = if is_bag_cnt then (fun x -> true) else is_sat in
          let (lhs,rhs) = rel_filter_assumption is_sat lhs rhs in
          (simplify_disj_new lhs,rhs) in      
        let pairwise_proc lhs =
          let lst = CP.split_conjunctions lhs in
          (* perform pairwise only for disjuncts *)
          let lst = List.map (fun e -> if CP.is_disjunct e then TP.pairwisecheck e else e) lst in
          CP.join_conjunctions lst
        in
        let wrap_exists (lhs,rhs) =
          let vs_r = CP.fv rhs in
          let vs_l = CP.fv lhs in
          let diff_vs = diff_svl vs_l (vs_r@rel_vars) in
          DD.devel_hprint (add_str "diff_vs" !print_svl) diff_vs pos;
          let new_lhs = CP.wrap_exists_svl lhs diff_vs in
          DD.devel_hprint (add_str "new_lhs (b4 elim_exists)" !CP.print_formula) new_lhs pos;
(*          let new_lhs = if is_bag_cnt then new_lhs else TP.simplify_raw new_lhs in*)
(*          DD.devel_hprint (add_str "new_lhs (aft elim_exists)" !CP.print_formula) new_lhs pos;*)
(*          let new_lhs = pairwise_proc (new_lhs) in*)
	  (*          (new_lhs,rhs) 
		      in*)
          (* TODO: Avoid generating redundant primed vars *)
          let new_lhs = if is_bag_cnt then pairwise_proc (CP.arith_simplify_new (CP.remove_red_primed_vars new_lhs))
            else
              let new_lhs_drop_rel = TP.simplify_raw (CP.drop_rel_formula new_lhs) in
              let new_lhs_drop_rel = pairwise_proc new_lhs_drop_rel in
              CP.conj_of_list (new_lhs_drop_rel::rel_lhs) no_pos 
          in
          let rel_def_id = CP.get_rel_id_list rhs in
          let rank_bnd_id = CP.get_rank_bnd_id_list rhs in
          let rank_dec_id = CP.get_rank_dec_and_const_id_list rhs in
          let rel_cat = 
            if rel_def_id != [] then CP.RelDefn (List.hd rel_def_id) else 
            if rank_bnd_id != [] then CP.RankBnd (List.hd rank_bnd_id) else
            if rank_dec_id != [] then CP.RankDecr rank_dec_id else
              report_error pos "Relation belongs to unexpected category"
          in
	  (*          if CP.intersect (CP.fv new_lhs_drop_rel) rel_vars = [] && rel_lhs != [] then 
		      (DD.devel_pprint ">>>>>> no recursive def <<<<<<" pos; [])
		      else*)
          (*if CP.isConstTrue new_lhs then [] else *)[(rel_cat,new_lhs,rhs)] in
        let inf_rel_ls = List.map (filter_ass lhs_2) rel_rhs in
        DD.trace_hprint (add_str "Rel Inferred (b4 pairwise):" (pr_list (fun (x,_) -> !CP.print_formula x))) inf_rel_ls pos;
        let inf_rel_ls = if is_bag_cnt then List.map (fun (lhs,rhs) -> (pairwise_proc lhs,rhs)) inf_rel_ls else inf_rel_ls in
        DD.trace_hprint (add_str "Rel Inferred (b4 wrap_exists):" (pr_list print_only_lhs_rhs)) inf_rel_ls pos;
	(*        let inf_rel_ls = List.map wrap_exists inf_rel_ls in*)
        let inf_rel_ls = List.concat (List.map wrap_exists inf_rel_ls) in
        (* TODO: Change corresponding vars for assumed pure *)
(*        let rel_cat_fml = List.hd rel_rhs in*)
(*        let assume_p  = estate.es_assumed_pure in*)
(*        let assume_rel_ls = List.map (fun ass_pure -> *)
(*          (CP.RelAssume (CP.get_rel_id_list rel_cat_fml), rel_cat_fml, ass_pure)) assume_p in*)
(*        DD.trace_hprint (add_str "Assume Pure :" (pr_list !CP.print_formula)) assume_p pos;*)
(*        DD.trace_hprint (add_str "rel_rhs :" (pr_list !CP.print_formula)) rel_rhs pos;*)
(*        DD.trace_hprint (add_str "rel_cat_fml :" (!CP.print_formula)) rel_cat_fml pos;*)
(*        DD.ninfo_hprint (add_str "Rel Inferred" (pr_list print_lhs_rhs)) inf_rel_ls pos;*)
(*        DD.ninfo_hprint (add_str "Rel Assume :" (pr_list (fun (_,a,b)->print_only_lhs_rhs (a,b)))) assume_rel_ls pos;*)
       (* let vars = stk_vars # get_stk in*)
	(* below causes non-linear LHS for relation *)
	(* let inf_rel_ls = List.map (simp_lhs_rhs vars) inf_rel_ls in *)
        (* DD.info_hprint (add_str "Rel Inferred (simplified)" (pr_list print_lhs_rhs)) inf_rel_ls pos; *)
        let estate = { estate with es_infer_rel = inf_rel_ls@(estate.es_infer_rel) } in
        if inf_rel_ls != [] then
          begin
            DD.devel_pprint ">>>>>> infer_collect_rel <<<<<<" pos;
            DD.devel_hprint (add_str "Infer Rel Ids" !print_svl) ivs pos;
            (* DD.devel_hprint (add_str "LHS heap Xpure1:" !print_mix_formula) xpure_lhs_h1 pos; *)
            DD.devel_hprint (add_str "LHS pure" !CP.print_formula) lhs_p pos;
            DD.devel_hprint (add_str "RHS pure" !CP.print_formula) rhs_p_n pos;
            DD.devel_hprint (add_str "RHS Rel List" (pr_list !CP.print_formula)) rel_rhs pos;
          end;
        (estate,lhs_p_orig,rhs_p_new)
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


let infer_collect_rel is_sat estate xpure_lhs_h1 (* lhs_h *) lhs_p (* lhs_b *) rhs_p pos =
  let pr0 x = !print_svl x.es_infer_vars_rel in
  let pr1 = !print_mix_formula in
  let pr2 (es,l,r) = pr_triple pr1 pr1 (pr_list CP.print_lhs_rhs) (l,r,es.es_infer_rel) in
      Debug.no_4 "infer_collect_rel" pr0 pr1 pr1 pr1 pr2
      (fun _ _ _ _ -> infer_collect_rel is_sat estate xpure_lhs_h1 (* lhs_h *) lhs_p (* lhs_b *) 
      rhs_p pos) estate xpure_lhs_h1 lhs_p rhs_p


(*=****************************************************************=*)
           (*=****************INFER REL HP ASS****************=*)
(*=*****************************************************************=*)
(*
1.  H(x) --> x::node<_,p>: p is forwarded
2.  H(x,y) --> x::node<_,p>: p and y are forwarded
3.  x::<_,p> * H (p) --> G(x): p is NOT forwarded
3a. z::node2<_,l,r> * HP_577(l) * G1(r) --> G1(z) : l,r are NOT forwarded
*)
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

let find_undefined_selective_pointers_x prog lfb rfb lmix_f rmix_f unmatched rhs_rest rhs_h_matched_set leqs reqs pos total_unk_map=
  let get_rhs_unfold_fwd_svl hd def_svl lhs_hpargs=
    if List.exists (fun (_,args) -> CP.mem_svl hd.CF.h_formula_data_node args) lhs_hpargs then
      let args = List.filter CP.is_node_typ hd.CF.h_formula_data_arguments in
      CP.remove_dups_svl (CP.diff_svl args def_svl)
    else []
  in
  let get_lhs_fold_fwd_svl selected_hps def_vs rhs_args lhs_hds ls_lhs_hpargs=
    (* let _ = DD.info_pprint (" rhs_args: " ^ (!CP.print_svl rhs_args)) pos in *)
    let rec find_pto cur_hds sv=
      match cur_hds with
        | [] -> []
        | hd::tl -> let ptr_args = List.filter CP.is_node_typ hd.CF.h_formula_data_arguments in
                    if CP.mem_svl sv ptr_args then [hd.CF.h_formula_data_node]
                    else find_pto tl sv
    in
    let process_one (hp,args)=
      if CP.mem_svl hp selected_hps then
        let not_fwd_slv = CP.remove_dups_svl (CP.diff_svl args (def_vs@rhs_args)) in
      (*check whether it is in form of lhs unfold*)
        let should_be_lhs_folded = List.map (fun sv -> sv,find_pto lhs_hds sv) not_fwd_slv in
        let ls_fwd_svl = List.map (fun (sv,ptos) -> if ptos <> [] && CP.diff_svl ptos rhs_args = [] then [] else [sv])
          should_be_lhs_folded in
        (List.concat ls_fwd_svl)
      else []
    in
    let ls_not_fwd_svl = List.map process_one ls_lhs_hpargs in
    (*should separate list of list *)
    CP.remove_dups_svl (List.concat ls_not_fwd_svl)
  in
  let find_well_defined_hp_x hds hvs (hp,args) def_ptrs lhsb=
    let closed_args = SAU.loop_up_closed_ptr_args prog hds hvs args in
    let undef_args = SAU.lookup_undef_args closed_args [] def_ptrs in
    if undef_args = [] then
      let f = SAU.keep_data_view_hrel_nodes_fb prog lhsb hds hvs args [hp] in
      ([(hp,args,f)],[])
    else
    ([],[(hp,args)])
  in
  let find_well_defined_hp hds hvs (hp,args) def_ptrs lhsb=
    let pr1 = !CP.print_sv in
    let pr2 = !CP.print_svl in
    let pr3 = pr_triple pr1 pr2 Cprinter.string_of_formula_base in
    let pr4 = (pr_pair pr1 pr2) in
    Debug.no_2 "find_well_defined_hp" pr4 pr2 (pr_pair (pr_list_ln pr3) (pr_list pr4))
        (fun _ _ -> find_well_defined_hp_x hds hvs (hp,args) def_ptrs lhsb) (hp,args) def_ptrs
  in
  let lookup_eq_linking_svl (hp0,args0) total_unk_map lhs_hpargs=
    let rec snd_assoc ls=
      match ls with
        | [] -> raise Not_found
        | (hp1,args1)::tl -> if SAU.eq_spec_var_order_list args1 args0 then
              hp1
            else snd_assoc tl
    in
    try
        let eq_hp = snd_assoc lhs_hpargs in
        let fr_args = List.assoc eq_hp total_unk_map in
        [(hp0,fr_args)]
    with Not_found ->
        []
  in
  (* DD.info_pprint ">>>>>> find_undefined_selective_pointers <<<<<<" pos; *)
  let lfb = CF.subst_b leqs lfb in
  let rfb = CF.subst_b leqs rfb in
  let lhds, lhvs, lhrs = CF.get_hp_rel_bformula lfb in
  let leqNulls = MCP.get_null_ptrs lmix_f in
  let rhds, rhvs, rhrs = CF.get_hp_rel_bformula rfb in
  let reqNulls = MCP.get_null_ptrs rmix_f in
  (* let hrs = (lhrs @ rhrs) in *)
  let hds = (lhds @ rhds) in
  let hvs = (lhvs @ rhvs) in
  let eqs = (leqs@reqs) in
   (*defined vars=  null + data + view + match nodes*)
  let def_vs = (leqNulls@reqNulls) @ (List.map (fun hd -> hd.CF.h_formula_data_node) hds)
   @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) (* @ rhs_h_matched_set *) in
  (*find closed defined pointers set*)
  (* let def_vs = CP.remove_dups_svl (List.fold_left SAU.close_def def_vs (eqs)) in *)
  let def_vs = CP.remove_dups_svl (SAU.find_close def_vs (eqs)) in
  (*selective*)
  let n_unmatched = CF.h_subst leqs unmatched in
  (*START debugging*)
  let _ = DD.ninfo_pprint (" n_lfb: " ^ (Cprinter.string_of_formula_base lfb)) pos in
  let _ = DD.ninfo_pprint (" n_unmatched: " ^ (Cprinter.string_of_h_formula n_unmatched)) pos in
  (*END debugging*)
  (* let n_lhds, _, n_lhrs = CF.get_hp_rel_bformula n_lfb in *)
  (**********get well-defined hp in lhs*)
  let helper (hp,eargs,_)=(hp,List.concat (List.map CP.afv eargs)) in
  let ls_lhp_args = (List.map helper lhrs) in
  let ls_defined_hps,rems = List.split (List.map (fun hpargs -> find_well_defined_hp hds hvs hpargs def_vs lfb) ls_lhp_args) in
  let defined_hps = List.concat ls_defined_hps in
  let rem_lhpargs = List.concat rems in
  (*END************get well-defined hp in lhs*)
  (*remove*)
  let unmatched_svl = SAU.get_ptrs unmatched in
  let unmatched_svl = (SAU.find_close  (unmatched_svl) (eqs)) in
  (* let _ = Debug.info_pprint ("    unmatched:" ^(!CP.print_svl unmatched_svl)) no_pos in *)
  let closed_unmatched_svl0 = List.concat (List.map (SAU.look_up_ptr_args_one_node prog hds hvs) unmatched_svl) in
  let closed_unmatched_svl = CP.remove_dups_svl
    (SAU.find_close  (unmatched_svl@closed_unmatched_svl0) (eqs)) in
  (*END selective*)
  (*get all args of hp_rel to check whether they are fully embbed*)
  (* let unmatched_hp_args = CF.get_HRels n_unmatched in *)
  let hp_args = rem_lhpargs(* @unmatched_hp_args *) in
  let selected_hp_args = List.filter (fun (_, args) -> (CP.intersect_svl args closed_unmatched_svl) != []) hp_args in
  let selected_hps0, hrel_args = List.split selected_hp_args in
  (*tricky here: since we dont have matching between two unk hps, we keep sth in rhs which not matched*)
  let rest_svl = CF.get_hp_rel_vars_h_formula rhs_rest in
  let rest_svl1 = SAU.find_close rest_svl leqs in
  let select_helper svl (hp,args)=
    (* let inter = CP.intersect_svl args svl in *)
    (* if inter = [] then [] *)
    (* else [(hp,inter)] *)
    if CP.diff_svl args svl = [] then [(hp,args)]
    else []
  in
  let drop_hpargs =  List.concat (List.map (select_helper rest_svl1) rem_lhpargs) in
  let drop_hps = fst (List.split drop_hpargs) in
  let selected_hps = CP.diff_svl selected_hps0 drop_hps in
  (*unknown svl*)
  let unk_svl,ps,unk_map = generate_linking_svl (List.filter (fun (hp0,_) -> CP.mem_svl hp0 selected_hps0) drop_hpargs) total_unk_map in
  (*========*)
  (*find undefined ptrs of all hrel args*)
  (*two cases: rhs unfold (mis-match is a node) and lhs fold (mis-match is a unk hp)*)
  let fwd_svl,rh_sel_hps,rhs_unk_map =
    if CF.is_HRel n_unmatched then
      let rhs_hpargs = CF.extract_HRel n_unmatched in
      (*depend we want to get framing spec*)
      let svl = (* if !Log.sleek_proving_kind = Log.POST then [] else *)
      (*since h_subst is not as expected we use closed set*)
            let closed_rhs_hpargs = SAU.find_close (snd rhs_hpargs) leqs in
            get_lhs_fold_fwd_svl selected_hps def_vs closed_rhs_hpargs lhds ls_lhp_args
      in
       (* let closed_svl = SAU.find_close svl leqs in *)
       DD.ninfo_pprint ("svl: " ^ (!CP.print_svl svl)) pos;
      let runk_map =lookup_eq_linking_svl rhs_hpargs total_unk_map selected_hp_args in
      (svl,[fst rhs_hpargs], runk_map)
    else
      let hds = SAU.get_hdnodes_hf n_unmatched in
      let hd =
        match hds with
          | [hd] -> hd
          | _ -> report_error no_pos "infer.find_undefined_selective_pointers"
      in
      let hrel_args1 = List.concat hrel_args in
  (*should include their closed ptrs*)
      let hrel_args2 = CP.remove_dups_svl (List.fold_left SAU.close_def hrel_args1 (eqs)) in
      let unfold_fwd_svl = get_rhs_unfold_fwd_svl hd (def_vs@hrel_args2) ls_lhp_args in
      (**)
      let l_args = List.concat (List.map (fun (_, exps, _) ->
      let r =List.concat (List.map CP.afv exps) in
      if (CP.intersect_svl r closed_unmatched_svl) != [] then r else []
  ) lhrs) in
      let r_args = List.concat (List.map (fun (_, exps, _) ->  List.concat (List.map CP.afv exps)) rhrs) in
      let r_args1 = (List.fold_left SAU.close_def r_args (leqs@reqs)) in
      let def_vsargs = List.concat (List.map (SAU.look_up_ptr_args_one_node prog hds hvs) def_vs) in
      let used_svl = CP.remove_dups_svl (def_vsargs@def_vs@r_args1) in
      let lundefs_args = CP.remove_dups_svl (CP.diff_svl l_args used_svl) in
      (unfold_fwd_svl@lundefs_args,[],[])
  in
  let undef =  CP.remove_dups_svl (fwd_svl) in
  DD.ninfo_pprint ("selected_hps: " ^ (!CP.print_svl (selected_hps))) pos;
  ((* undefs1@lundefs_args *) undef,hds,hvs,lhrs,rhrs,leqNulls@reqNulls,selected_hps,rh_sel_hps, defined_hps,
  unk_svl,ps,unk_map@rhs_unk_map)

let find_undefined_selective_pointers prog lfb rfb lmix_f rmix_f unmatched rhs_rest rhs_h_matched_set leqs reqs pos total_unk_map=
  let pr1 = Cprinter.string_of_formula_base in
  let pr2 = Cprinter.prtt_string_of_h_formula in
  (* let pr2 = !print_svl in *)
  (* let pr3 =  pr_pair string_of_typ !print_sv in *)
  let pr4 = pr_list !print_sv in
  let pr6 = pr_list_ln (pr_triple !CP.print_sv !CP.print_svl Cprinter.string_of_formula_base) in
  let pr5 = fun (undefs,_,_,_,_,_,_,_,defined_hps,_,_,_) -> let pr = pr_pair pr4 pr6 in pr (undefs,defined_hps) in
  Debug.no_4 "find_undefined_selective_pointers" pr2 !print_svl pr1 pr1 pr5
( fun _ _ _ _-> find_undefined_selective_pointers_x prog lfb rfb lmix_f rmix_f unmatched rhs_rest
    rhs_h_matched_set leqs reqs pos total_unk_map) unmatched rhs_h_matched_set lfb rfb


(*
out: list of program variables of mismatching node
*)
let get_prog_vars_x prog_hps rhs_unmatch proving_kind=
  match rhs_unmatch with
    | CF.HRel (hp, eargs,_) ->
        if proving_kind = Log.POST && CP.mem_svl hp prog_hps then
          (List.fold_left List.append [] (List.map CP.afv eargs))
        else []
    | _ -> []

let get_prog_vars prog_hps rhs_unmatch proving_kind=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.string_of_h_formula in
  let pr3 = Log.string_of_sleek_proving_kind in
  Debug.no_3 "get_prog_vars" pr1 pr2 pr3 pr1
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
let simplify_lhs_rhs prog lhs_b rhs_b leqs reqs hds hvs lhrs rhrs lhs_selected_hps rhs_selected_hps crt_holes history unk_svl prog_vars=
  let look_up_lhs_root_first_var (_,args)=
    (* let _ = Debug.info_pprint ("    args:" ^ (!CP.print_svl hd) ^ ": "^(!CP.print_svl args)) no_pos in *)
    List.hd args
  in
  let filter_non_selected_hp selected_hps (hp,eargs)= CP.mem_svl hp selected_hps in
  (*lhs*)
  let l_hpargs = List.map (fun (hp,eargs,_) -> (hp, (CP.remove_dups_svl (List.concat (List.map CP.afv eargs)))) ) lhrs in
  let lhp_args,l_rem_hp_args = (List.partition (filter_non_selected_hp lhs_selected_hps) l_hpargs) in
  let lkeep_hrels,lhs_keep_rootvars = List.split lhp_args in
  let lhs_keep_rootvars = List.concat lhs_keep_rootvars in
  let lhs_keep_first_rootvars = (List.map look_up_lhs_root_first_var lhp_args) in
  (*rhs*)
  let r_hpargs = CF.get_HRels rhs_b.CF.formula_base_heap in
  let rhp_args,r_rem_hp_args = (List.partition (filter_non_selected_hp rhs_selected_hps) r_hpargs) in
  let rkeep_hrels, keep_rootvars = List.split rhp_args in
  let keep_hrels = (lkeep_hrels@rkeep_hrels) in
  let rhs_keep_rootvars = List.concat keep_rootvars in
  (***************************)
  (*w history*)
  let svl = (CP.remove_dups_svl (lhs_keep_first_rootvars@rhs_keep_rootvars)) in
  let svl = (List.fold_left SAU.close_def svl (leqs@reqs)) in
  (*for wo history*)
  (* let history = [] in *)
  (*get args which already captures by other hprel*)
  let done_args = CP.remove_dups_svl (List.concat (List.map (fun (_,args) -> args) (lhp_args))) in
  let lhs_b,history_hrel,keep_root_hrels,his_ss = get_history_nodes svl hds history lhs_b done_args (leqs@reqs) lhp_args in
  (*from history, we can keep more svl, hprels*)
  let keep_his_svl = CP.remove_dups_svl (List.fold_left SAU.close_def (svl@keep_root_hrels) his_ss) in
  (* let _ = Debug.info_pprint ("    keep_his_svl:" ^(!CP.print_svl keep_his_svl)) no_pos in *)
  let keep_his_hps = List.concat (List.map (fun (hp,args) -> if CP.diff_svl args keep_his_svl = [] then [hp] else [])
                                     (l_rem_hp_args@r_rem_hp_args)) in
 (*end*)
  let keep_hrels1 = (CP.remove_dups_svl (keep_hrels(* @history_hrel@keep_his_hps *))) in
  (* let lkeep_hrels = CP.remove_dups_svl (lkeep_hrels@history_hrel@keep_his_hps) in *)
  (*END*)
  let rec elim_redun_his his res=
    match his with
      | [] -> res
      | hd:: tl ->
          let svl0 = SAU.find_close [hd.CF.h_formula_data_node] leqs in
          if List.exists
            (fun hd1 -> CP.mem_svl hd1.CF.h_formula_data_node svl0) hds then
            elim_redun_his tl res
          else elim_redun_his tl (res@[hd])
  in
  let filter_his = elim_redun_his (List.concat (List.map get_h_formula_data_fr_hnode history)) [] in
  let _ = Debug.ninfo_pprint ("    keep_hrels1:" ^(!CP.print_svl keep_hrels1)) no_pos in
  let lhs_b1,rhs_b1 = SAU.keep_data_view_hrel_nodes_two_fbs prog lhs_b rhs_b
    (hds@filter_his) hvs (lhp_args@rhp_args) leqs reqs (* his_ss *) []
    (* (rhs_keep_rootvars@lhs_keep_first_rootvars) *)(svl@keep_root_hrels) (lhs_keep_rootvars@keep_root_hrels)
    lkeep_hrels rkeep_hrels unk_svl prog_vars in
  (*wo history*)
  (* let lhs_b1,rhs_b1 = SAU.keep_data_view_hrel_nodes_two_fbs prog lhs_b rhs_b *)
  (*   hds hvs (leqs@reqs) *)
  (*   (rhs_keep_rootvars@lhs_keep_first_rootvars) lhs_keep_rootvars keep_hrels in *)
  (***************************)
  (*subst holes*)
  let lhs_b1 = {lhs_b1 with CF.formula_base_heap = IMM.apply_subs_h_formula crt_holes lhs_b1.CF.formula_base_heap} in
  let rhs_b1 = {rhs_b1 with CF.formula_base_heap = IMM.apply_subs_h_formula crt_holes rhs_b1.CF.formula_base_heap} in
  (*remove equals. args of one hp must be diff*)
  (* let filter_helper ls ls_hp_args= *)
  (*   List.exists (fun (_,ls1) -> (Gen.BList.difference_eq CP.eq_spec_var ls ls1) = []) ls_hp_args *)
  (* in *)
  (* let rec elim_eqs_args eqs hp_args= *)
  (*   List.filter (fun (v1,v2) -> not(filter_helper [v1;v2] hp_args)) eqs *)
  (* in *)
  let lhs_b2 = (* CF.subst_b (nleqs) *) lhs_b1 in (*m_apply_par*)
  let rhs_b2 = (* CF.subst_b (nleqs@nreqs) *) rhs_b1 in
  (* let _ = Debug.info_pprint ("lhs_b2: " ^ (Cprinter.string_of_formula_base lhs_b2)) no_pos in *)
  (* let _ = Debug.info_pprint ("rhs_b2: " ^ (Cprinter.string_of_formula_base rhs_b2)) no_pos in *)
  (*remove redundant: x=x*)
  let lhs_b3 = {lhs_b2 with CF.formula_base_pure = MCP.mix_of_pure
      (CP.remove_redundant (MCP.pure_of_mix lhs_b2.CF.formula_base_pure))} in
  let rhs_b3 = {rhs_b2 with CF.formula_base_pure = MCP.mix_of_pure
      (CP.remove_redundant (MCP.pure_of_mix rhs_b2.CF.formula_base_pure))} in
  (*args of one hp must be diff --
       inside SAU.keep_data_view_hrel_nodes_two_fbs*)
  (* let lhs_b4,rhs_b4 = SAU.rename_hp_args lhs_b3 rhs_b3 in *)
  (lhs_b3,rhs_b3)

(*
type: Cast.prog_decl ->
  Cformula.entail_state ->
  SAU.CF.h_formula ->
  CP.spec_var list ->
  CF.formula_base -> CF.formula_base -> Globals.loc -> bool * CF.entail_st
*)
let infer_collect_hp_rel_x prog (es:entail_state) rhs rhs_rest (rhs_h_matched_set:CP.spec_var list) lhs_b rhs_b pos =
  let generate_hp_ass pred rf (hp,args,lfb) =
    {
        CF.hprel_kind = CP.RelAssume [hp];
        unk_svl = [];(*inferred from norm*)
        unk_hps = [];
        predef_svl = pred;
        hprel_lhs = CF.Base lfb;
        hprel_rhs = rf;
    }
  in
  (*for debugging*)
  (* DD.info_pprint ("  es: " ^ (Cprinter.string_of_formula es.CF.es_formula)) pos; *)
  let _ = Debug.ninfo_pprint ("es_infer_vars_hp_rel: " ^ (!CP.print_svl  es.es_infer_vars_hp_rel)) no_pos in
  let _ = Debug.ninfo_pprint ("es_infer_vars_sel_hp_rel: " ^ (!CP.print_svl  es.es_infer_vars_sel_hp_rel)) no_pos in
  (*end for debugging*)
  if no_infer_hp_rel es then (false, es)
  else
    let ivs = es.es_infer_vars_hp_rel in
    (*check whether LHS/RHS contains hp_rel*)
    let lhrs = CF.get_hp_rel_name_bformula lhs_b in
    let rhrs = CF.get_hp_rel_name_bformula rhs_b in
    if CP.intersect ivs (lhrs@rhrs) = [] then
      begin
        (* DD.info_pprint ">>>>>> infer_hp_rel <<<<<<" pos; *)
        DD.ninfo_pprint " no hp_rel found" pos;
        (false,es)
      end
    else
      begin
        (* DD.info_pprint "  hp_rel found" pos; *)
        (*which pointers are defined and which arguments of data nodes are pointer*)
        let ( _,mix_lf,_,_,_) = CF.split_components (CF.Base lhs_b) in
        let (_,mix_rf,_,_,_) = CF.split_components (CF.Base rhs_b) in
        let leqs = (MCP.ptr_equations_without_null mix_lf) (* @ (MCP.ptr_equations_with_null mix_lf) *) in
        let reqs = es.CF.es_rhs_eqset (* @ (MCP.ptr_equations_with_null mix_rf) *) in
        let _ =
          (* let pr_elem = Cpure.SV.string_of in *)
          (* let pr2 = pr_list (pr_pair pr_elem pr_elem) in *)
          DD.ninfo_pprint ">>>>>> infer_hp_rel <<<<<<" pos;
          DD.ninfo_pprint ("  es_heap: " ^ (Cprinter.string_of_h_formula es.CF.es_heap)) pos;
          DD.ninfo_pprint ("  footprint: " ^ (let pr=pr_list_ln Cprinter.string_of_h_formula in pr es.CF.es_history)) pos;
          DD.ninfo_pprint ("  lhs: " ^ (Cprinter.string_of_formula_base lhs_b)) pos;
          DD.ninfo_pprint ("  rhs: " ^ (Cprinter.string_of_formula_base rhs_b)) pos;
          DD.ninfo_pprint ("  unmatch: " ^ (Cprinter.string_of_h_formula rhs)) pos;
          (* DD.info_pprint ("  lhs aliases: " ^  (pr2 leqs)) pos; (\* aliases from LHS *\) *)
          (* DD.info_pprint ("  rhs aliases: " ^  (pr2 reqs)) pos;  (\* aliases from LHS *\) *)
        in
        let mis_nodes =  match rhs with
          | DataNode n -> [n.h_formula_data_node]
          | ViewNode n -> [n.h_formula_view_node]
          | HRel (_,eargs,_) -> CP.remove_dups_svl (List.concat (List.map CP.afv eargs))
          | _ -> report_error pos "Expect a node or a hrel"
          (* CF.get_ptr_from_data_w_hrel *)
        in
        (* let _, lhs_sel_vars = (List.split (CF.get_HRels lhs_b.CF.formula_base_heap)) in *)
        (* let lhs_sel_vars =  List.concat lhs_sel_vars in *)
        (* let lhs_sel_vars = ((CF.h_fv lhs_b.CF.formula_base_heap)) in *)
         let lhs_sel_vars = (CF.fv (CF.Base lhs_b)) in
        if (CP.intersect mis_nodes (List.fold_left SAU.close_def lhs_sel_vars leqs)) = [] then
          (
              Debug.info_pprint ">>>>>> mismatch ptr is not a selective variable <<<<<<" pos;
              (false,es))
        else
          (*generate new heap pred with undefined pointers only*)
          (* let _ = DD.info_pprint ">>>>>> generate new hp_rel with undefined selective pointers only <<<<<<" pos in *)
          (* let pr = pr_list (pr_pair !CP.print_sv !CP.print_svl) in *)
          (* let _ = DD.info_pprint ("  es_infer_hp_unk_map: " ^ (pr es.CF.es_infer_hp_unk_map) ) pos in *)
          let his_ptrs = List.concat (List.map SAU.get_ptrs es.CF.es_history) in
          let unknown_ptrs,hds,hvs,lhras,rhras,eqNull,lselected_hps,rselected_hps,defined_hps,unk_svl,unk_pure,unk_map =
            find_undefined_selective_pointers prog lhs_b rhs_b  mix_lf mix_rf rhs rhs_rest
                (rhs_h_matched_set@his_ptrs) leqs reqs pos es.CF.es_infer_hp_unk_map in
          let update_fb fb =
            match unknown_ptrs with
              | [] -> fb,[],[],None
              | _ -> let (hf,vhp_rels) = SAU.add_raw_hp_rel prog unknown_ptrs pos in
                  begin
                      match hf with
                        | HRel hp ->
                            (CF.mkAnd_fb_hf fb hf pos), [vhp_rels],[hp],(Some (hf,vhp_rels))
                        | _ -> report_error pos "infer.infer_collect_hp_rel_x: add_raw_hp_rel should return a hrel"
                  end
          in
          let new_rhs_b,rvhp_rels,new_hrels,r_new_hp = update_fb rhs_b in
          (*add roots from history*)
		  let matched_svl = CF.get_ptrs es.CF.es_heap in
		  let matched_svl1 = (List.fold_left SAU.close_def matched_svl (leqs@reqs)) in
		  let sel_his = List.concat (List.map (fun hf -> match hf with
            | CF.DataNode hd -> if CP.mem_svl hd.CF.h_formula_data_node matched_svl1 then [] else [hf]
			| _ -> [hf]
			) es.CF.es_history) in
          let lhs_b0 = CF.mkAnd_base_pure lhs_b (MCP.mix_of_pure unk_pure) pos in
          let group_unk_svl = List.concat (List.map (fun ass -> ass.CF.unk_svl) Log.current_hprel_ass_stk # get_stk) in
          let total_unk_svl = CP.remove_dups_svl (group_unk_svl@unk_svl) in
          let prog_vars = get_prog_vars es.CF.es_infer_vars_sel_hp_rel rhs !Log.sleek_proving_kind in
          let (new_lhs_b,new_rhs_b) = simplify_lhs_rhs prog lhs_b0 new_rhs_b leqs reqs hds hvs lhras (rhras@new_hrels)
            (lselected_hps) (rselected_hps@(List.map (fun (hp,_,_) -> hp) new_hrels)) es.CF.es_crt_holes ((* es.CF.es_heap:: *)(*es.CF.es_history*) sel_his) total_unk_svl prog_vars in
          (*simply add constraints: *)
          let hprel_def = List.concat (List.map CF.get_ptrs (es.CF.es_history@(CF.get_hnodes es.CF.es_heap))) in
          let closed_hprel_def = CP.subst_var_list (leqs@reqs) hprel_def in
          let closed_hprel_args_def,_,_,_,_ = SAU.find_defined_pointers_after_preprocess prog closed_hprel_def
            (hds@(List.concat (List.map get_h_formula_data_fr_hnode es.CF.es_history)))
            hvs (lhras@rhras@new_hrels) (leqs@reqs) [] in
          let rf = CF.mkTrue (CF.mkTrueFlow()) pos in
          let defined_hprels = List.map (generate_hp_ass (closed_hprel_args_def@total_unk_svl) rf) defined_hps in
          let hp_rel = {
              CF.hprel_kind = CP.RelAssume (CP.remove_dups_svl (lhrs@rhrs@rvhp_rels));
              unk_svl = total_unk_svl;(*inferred from norm*)
              unk_hps = [];
              predef_svl = (closed_hprel_args_def@total_unk_svl);
              hprel_lhs = CF.Base new_lhs_b;
              hprel_rhs = CF.Base new_rhs_b;
          } in
          let _ = rel_ass_stk # push_list ([hp_rel]@defined_hprels) in
          let _ = Log.current_hprel_ass_stk # push_list ([hp_rel]@defined_hprels) in
          DD.ninfo_pprint ("  hp_rels: " ^ (let pr = pr_list_ln Cprinter.string_of_hprel in pr (defined_hprels@ [hp_rel]))) pos;
          let update_es_f f new_hp=
            match new_hp with
              | None -> f
              | Some (hf,vhp_rels) -> (CF.mkAnd_f_hf f (CF.h_subst leqs hf) pos)
          in
          (*update the residue*)
          let new_es_formula =  update_es_f es.CF.es_formula r_new_hp in
          let new_es_formula = CF.mkAnd_pure new_es_formula (MCP.mix_of_pure unk_pure) (CF.pos_of_formula new_es_formula) in
          (*drop hp rel + nodes consumed in lhs of hp_rel in es_formula*)
          (* DD.info_pprint ("  before: " ^ (Cprinter.string_of_formula new_es_formula)) pos; *)
          let root_vars_ls = SAU.get_data_view_hrel_vars_bformula new_lhs_b in
          (*tricky here: since we dont have matching between two unk hps, we keep sth in rhs which not matched*)
          let rest_svl = CF.get_hp_rel_vars_h_formula rhs_rest in
          let rest_svl1 = SAU.find_close rest_svl leqs in
          let new_hp_args = CF.get_HRels new_lhs_b.CF.formula_base_heap in
          let check_full_inter svl (hp,args)=
            if CP.diff_svl args svl = [] then [hp] else []
          in
          let keep_hps =  List.concat (List.map (check_full_inter rest_svl1) new_hp_args) in
          (* let _ = DD.info_pprint ("  rest_svl1: " ^ (!CP.print_svl rest_svl1)) pos in *)
          (* let _ = DD.info_pprint ("  keep_hps: " ^ (!CP.print_svl keep_hps)) pos in *)
          let root_vars_ls1 = CP.diff_svl root_vars_ls keep_hps in
          let well_defined_svl = List.concat (List.map (fun (hp,args,_) -> hp::args) defined_hps) in
          let new_es_formula = SAU.drop_data_view_hrel_nodes_from_root prog new_es_formula hds hvs leqs root_vars_ls1 well_defined_svl in
            (*CF.drop_hrel_f new_es_formula lhrs in *)
          (*add mismatched heap into the entail states if @L*)
          let check_consumed_node h f= 
            match h with
              | DataNode hd -> if not(CF.isLend (hd.CF.h_formula_data_imm)) then f else
                    let new_h = DataNode {hd with CF.h_formula_data_imm = (CF.ConstAnn(Mutable));} in
                    CF.mkAnd_f_hf f new_h pos
              | _ -> f
          in
          let new_es_formula = check_consumed_node rhs new_es_formula in
          let new_es = {es with CF. es_infer_vars_hp_rel = es.CF.es_infer_vars_hp_rel@rvhp_rels;
              CF.es_infer_hp_rel = es.CF.es_infer_hp_rel @ defined_hprels @ [hp_rel];
              CF.es_infer_hp_unk_map = (es.CF.es_infer_hp_unk_map@unk_map);
              CF.es_formula = new_es_formula} in
          DD.ninfo_pprint ("  new lhs: " ^ (Cprinter.string_of_formula new_es.CF.es_formula)) pos;
          (true, new_es)
      end

let infer_collect_hp_rel prog (es:entail_state) rhs rhs_rest (rhs_h_matched_set:CP.spec_var list) lhs_b rhs_b pos =
  let pr1 = Cprinter.string_of_formula_base in
  let pr4 = Cprinter.string_of_estate_infer_hp in
  let pr5 =  pr_pair string_of_bool pr4 in
  Debug.no_2 "infer_collect_hp_rel" pr1 pr1 pr5
( fun _ _ -> infer_collect_hp_rel_x prog es rhs rhs_rest rhs_h_matched_set lhs_b rhs_b pos) lhs_b rhs_b

(*=*****************************************************************=*)
         (*=**************INFER REL HP ASS*****************=*)
(*=*****************************************************************=*)

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

let print_spec spec file_name =
  let output_spec = file_name ^ ".spec" in
  let oc = open_out output_spec in
  Printf.fprintf oc "%s" spec;
  flush oc;
  close_out oc;;

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
  let res = Parser.parse_spec input_str in
  (*  print_endline ("SPEC" ^ (Iprinter.string_of_struc_formula res));*)
(*  let id,command = get_cmd_from_file in*)
  let id, command = !(IF.cmd) in
  let cmd = match command with
    | (true,_,Some view_node) -> 
      let proc = List.filter (fun x -> x.I.proc_name=id) prog.I.prog_proc_decls in
      let keep_vars = 
        if List.length proc != 1 then report_error no_pos "Error in get_spec_from_file"
        else 
          List.map (fun x -> x.I.param_name) (List.hd proc).I.proc_args
      in
      let _ = get_shape_from_file view_node keep_vars id in
      IF.mkETrue top_flow no_pos
    | (false,Some cmd,_) -> cmd
    | _ -> report_error no_pos "Error in get_spec_from_file"
  in
  let res = List.map (fun (id1,spec) -> 
    if id1=id then (id1,IF.merge_cmd cmd spec) else (id1,spec)) res in
  res

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

