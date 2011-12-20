open Globals
module DD = Debug
open Gen
open Exc.GTable
open Perm
open Cformula
open Context
open Cpure

module Err = Error
module CP = Cpure
module MCP = Mcpure
module CF = Cformula

let no_infer estate = (estate.es_infer_vars == [])
 
let remove_infer_vars_all estate =
  let iv = estate.es_infer_vars in
   ({estate with es_infer_vars=[];}, iv) 

let remove_infer_vars_partial estate rt =
  let iv = estate.es_infer_vars in
  if (iv==[]) then (estate,iv)
  else ({estate with es_infer_vars=CP.diff_svl iv rt;}, iv) 

let remove_infer_vars_partial estate rt =
  let pr1 = !print_entail_state in
  let pr2 = !print_svl in
  Gen.Debug.no_2 "remove_infer_vars_partial" pr1 pr2 (pr_pair pr1 pr2) 
      remove_infer_vars_partial estate rt 

let rec remove_infer_vars_all_ctx ctx =
  match ctx with
  | Ctx estate -> 
        let (es,_) = remove_infer_vars_all estate in
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

(* let collect_pre_heap_list_partial_context (ctx:list_partial_context) = *)
(*   let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c) -> collect_pre_heap c) cl))  ctx in *)
(*   List.concat r *)

let rec restore_infer_vars_ctx iv ctx = 
  match ctx with
  | Ctx estate -> 
        if iv==[] then ctx
        else Ctx {estate with es_infer_vars=iv;}
  | OCtx (ctx1, ctx2) -> OCtx (restore_infer_vars_ctx iv ctx1, restore_infer_vars_ctx iv ctx2)

let restore_infer_vars iv cl =
  if (iv==[]) then cl
  else match cl with
    | FailCtx _ -> cl
    | SuccCtx lst -> SuccCtx (List.map (restore_infer_vars_ctx iv) lst)

let rec get_all_args alias_of_root heap = match heap with
  | ViewNode h -> h.h_formula_view_arguments
  | Star s -> (get_all_args alias_of_root s.h_formula_star_h1) @ (get_all_args alias_of_root s.h_formula_star_h2)
  | Conj c -> (get_all_args alias_of_root c.h_formula_conj_h1) @ (get_all_args alias_of_root c.h_formula_conj_h1)
  | Phase p -> (get_all_args alias_of_root p.h_formula_phase_rd) @ (get_all_args alias_of_root p.h_formula_phase_rw) 
  | _ -> []

let is_inferred_pre estate = 
  let r = (List.length (estate.es_infer_heap))+(List.length (estate.es_infer_pure)) in
  if r>0 then true else false

let rec is_inferred_pre_ctx ctx = 
  match ctx with
  | Ctx estate -> is_inferred_pre estate 
  | OCtx (ctx1, ctx2) -> (is_inferred_pre_ctx ctx1) || (is_inferred_pre_ctx ctx2)

let is_inferred_pre_list_context ctx = 
  match ctx with
  | FailCtx _ -> false
  | SuccCtx lst -> List.exists is_inferred_pre_ctx lst

let is_inferred_pre_list_context ctx = 
  Gen.Debug.no_1 "is_inferred_pre_list_context"
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

let rec init_vars ctx infer_vars orig_vars = match ctx with
  | Ctx estate -> Ctx {estate with es_infer_vars = infer_vars; es_orig_vars = orig_vars}
  | OCtx (ctx1, ctx2) -> OCtx (init_vars ctx1 infer_vars orig_vars, init_vars ctx2 infer_vars orig_vars)

(*let conv_infer_heap hs =
  let rec helper hs h = match hs with
    | [] -> h
    | x::xs -> 
      let acc = 
	    Star({h_formula_star_h1 = x;
	      h_formula_star_h2 = h;
	      h_formula_star_pos = no_pos})
        in helper xs acc in
  match hs with
    | [] -> HTrue 
    | x::xs -> helper xs x

let extract_pre_list_context x = 
  (* TODO : this has to be implemented by extracting from es_infer_* *)
  (* print_endline (!print_list_context x); *)
  None*)

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
  match h with
    | DataNode h -> 
          let h = to_unprimed_data_root aset h in
          let root = h.h_formula_data_node in
          let arg = h.h_formula_data_arguments in
          let new_arg = CP.fresh_spec_vars_prefix "inf" arg in
         Some (root, arg,new_arg, 
         DataNode {h with h_formula_data_arguments=new_arg;})
    | ViewNode h -> 
          let h = to_unprimed_view_root aset h in
          let root = h.h_formula_view_node in
          let arg = h.h_formula_view_arguments in
          let new_arg = CP.fresh_spec_vars_prefix "inf" arg in
          Some (root, arg,new_arg,
          ViewNode {h with h_formula_view_arguments=new_arg;} )
    | _ -> None

(*
type: Cformula.h_formula ->
  (Cformula.CP.spec_var * Cformula.CP.spec_var list * CP.spec_var list *
   Cformula.h_formula)
  option
*)
let get_args_h_formula aset (h:h_formula) =
  let pr1 = !print_h_formula in
  let pr2 = pr_option (pr_quad !print_sv !print_svl !print_svl pr1) in
  Gen.Debug.no_1 "get_args_h_formula" pr1 pr2 (fun _ -> get_args_h_formula aset h) h

let get_alias_formula (f:CF.formula) =
  let (h, p, fl, b, t) = split_components f in
  let eqns = (MCP.ptr_equations_without_null p) in
  eqns

(* let get_alias_formula (f:CF.formula) = *)
(*   Gen.Debug.no_1 "get_alias_formula" !print_formula !print_pure_f get_alias_formula f *)

let build_var_aset lst = CP.EMapSV.build_eset lst

let is_elem_of conj conjs = 
  let filtered = List.filter (fun c -> Omega.imply conj c "1" 100 && Omega.imply c conj "2" 100) conjs in
  match filtered with
    | [] -> false
    | _ -> true

(*
 let iv = es_infer_vars in
 check if h_formula root isin iv
 if not present then 
  begin
    (i) look for le = lhs_pure based on iv e.g n=0
        e.g. infer [n] n=0 |- x::node<..>
   (ii) if le=true then None
        else add not(le) to infer_pure
  end
 else 
  begin
   check if rhs causes a contradiction with estate
      e.g. infer [x] x=null |- x::node<..>
      if so then
           ?
      else
         add h_formula to infer_heap
  end
*)

let infer_heap_nodes (es:entail_state) (rhs:h_formula) rhs_rest conseq = 
  if no_infer es then None
  else 
    let iv = es.es_infer_vars in
    let lhs_als = get_alias_formula es.es_formula in
    let lhs_aset = build_var_aset lhs_als in
    let rt = get_args_h_formula lhs_aset rhs in
    (*let rhs_als = get_alias_formula conseq in
    let rhs_aset = build_var_aset rhs_als in*)
    let (b,args,inf_vars,new_h,new_iv,alias,r) = match rt with (* is rt captured by iv *)
      | None -> false,[],[],HTrue,iv,[],[]
      | Some (r,args,arg2,h) -> 
            let alias = CP.EMapSV.find_equiv_all r lhs_aset in
            (*let rt_al = [r]@alias in (* set of alias with root of rhs *)*)
            (*let b = not((CP.intersect iv rt_al) == []) in (* does it intersect with iv *)*)
            (* let new_iv = (CP.diff_svl (arg2@iv) rt_al) in *)
            let new_iv = arg2@iv in
            let alias = if List.mem r iv then [] else alias in
            (List.exists (CP.eq_spec_var_aset lhs_aset r) iv,args,arg2,h,new_iv,alias,[r]) in
    (*let args_al = List.map (fun v -> CP.EMapSV.find_equiv_all v rhs_aset) args in*)
    (* let _ = print_endline ("infer_heap_nodes") in *)
    (* let _ = print_endline ("infer var: "^(!print_svl iv)) in *)
    (* let _ = print_endline ("new infer var: "^(!print_svl new_iv)) in *)
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
    if b then 
      begin
        (* Take the alias as the inferred pure *)
        let iv_al = CP.intersect iv alias in (* All relevant vars of interest *)
        let iv_al = CP.diff_svl iv_al r in
        (* r certainly has one element *)
        let r = List.hd r in
        let r = CP.mkVar r no_pos in
        let new_p = Omega.simplify (List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) 
            (CP.mkTrue no_pos) 
            (List.map (fun a -> CP.BForm (CP.mkEq_b (CP.mkVar a no_pos) r no_pos, None)) iv_al)) in
        let lhs_h,_,_,_,_ = CF.split_components es.es_formula in
        let _,ante_pure,_,_,_ = CF.split_components es.es_orig_ante in
        let ante_conjs = CP.list_of_conjs (MCP.pure_of_mix ante_pure) in
        let new_p_conjs = CP.list_of_conjs new_p in
        let new_p = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) (CP.mkTrue no_pos)
          (List.filter (fun c -> not (is_elem_of c ante_conjs)) new_p_conjs) in
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
            Some (new_iv,new_h,new_p))
      end
    else None

(*
type: Cformula.entail_state ->
  Cformula.h_formula ->
  Cformula.h_formula ->
  'a -> (Cformula.CP.spec_var list * Cformula.h_formula * CP.formula) option
*)
let infer_heap_nodes (es:entail_state) (rhs:h_formula) rhs_rest conseq = 
  let pr1 = !print_entail_state in
  let pr2 = !print_h_formula in
  let pr3 = pr_option (pr_triple !print_svl pr2 !print_pure_f) in
  Gen.Debug.no_2 "infer_heap_nodes" pr1 pr2 pr3
      (fun _ _ -> infer_heap_nodes es rhs rhs_rest conseq) es rhs

(* picks ctr from f that are related to vars *)
(* may involve a weakening process *)
let rec filter_var f vars = match f with
  | CP.Or (f1,f2,l,p) -> 
        CP.Or (filter_var f1 vars, filter_var f2 vars, l, p)
  | _ -> 
        if Omega.is_sat f "0" 
        then CP.filter_var f vars 
        else CP.mkFalse no_pos

let filter_var f vars =
  let pr = !print_pure_f in
  Gen.Debug.no_2 "i.filter_var" pr !print_svl pr filter_var f vars 

(* TODO : this simplify could be improved *)
let simplify f vars = Omega.simplify (filter_var (Omega.simplify f) vars)
let simplify_contra f vars = filter_var f vars

let simplify f vars =
  let pr = !print_pure_f in
  Gen.Debug.no_2 "i.simplify" pr !print_svl pr simplify f vars 

let infer_lhs_contra lhs_xpure ivars =
  (* if ivars==[] then None *)
  (* else *)
    let lhs_xpure = MCP.pure_of_mix lhs_xpure in
    let check_sat = Omega.is_sat lhs_xpure "0" in
    if not(check_sat) then None
    else 
      let f = simplify_contra lhs_xpure ivars in
      let vf = CP.fv f in
      let over_v = CP.intersect vf ivars in
      if (over_v ==[]) then None
      else 
        let exists_var = CP.diff_svl vf ivars in
        let f = CP.mkExists_with_simpl_debug Omega.simplify exists_var f None no_pos in
        if CP.isConstTrue f then None
        else Some (Redlog.negate_formula f)

let infer_lhs_contra f ivars =
  let pr = !print_mix_formula in
  let pr2 = !print_pure_f in
  Gen.Debug.no_2 "infer_lhs_contra" pr !print_svl (pr_option pr2) infer_lhs_contra f ivars

let infer_lhs_contra_estate estate lhs_xpure pos =
  if no_infer estate then None
  else
    let ivars = estate.es_infer_vars in
    let r = infer_lhs_contra lhs_xpure ivars in
    match r with
      | None -> None
      | Some pf ->
            let new_estate =
              {estate with 
                  es_formula = normalize 0 estate.es_formula (CF.formula_of_pure_formula pf pos) pos;
                  es_infer_pure = estate.es_infer_pure@[pf];
              } in
            Some (new_estate,pf)

let infer_lhs_contra_estate e f pos =
  let pr0 = !print_entail_state in
  let pr = !print_mix_formula in
  Gen.Debug.no_2 "infer_lhs_contra_estate" pr0 pr (pr_option pr0) (fun _ _ -> infer_lhs_contra_estate e f pos) e f

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
(*   Gen.Debug.no_3 "infer_lhs_rhs_pure" pr pr !print_svl (pr_option pr) infer_lhs_rhs_pure lhs rhs ivars *)

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

let rec simplify_disjs pf lhs rhs = 
  let helper fml lhs_p rhs_p = 
    let new_fml = CP.mkAnd (CP.mkAnd fml lhs_p no_pos) rhs_p no_pos in
    if Omega.is_sat new_fml "0" then 
      let args = CP.fv new_fml in
      let iv = CP.fv fml in
      let quan_var = CP.diff_svl args iv in
      CP.mkExists_with_simpl_debug Omega.simplify quan_var new_fml None no_pos
    else CP.mkFalse no_pos
  in 
  match pf with
  | BForm _ -> if CP.isConstFalse pf then pf else helper pf lhs rhs
  | And _ -> helper pf lhs rhs
  | Or (f1,f2,l,p) -> Or (simplify_disjs f1 lhs rhs, simplify_disjs f2 lhs rhs, l, p)
  | _ -> pf

let infer_pure_m estate lhs_xpure rhs_xpure pos =
  if no_infer estate then None
  else
    let lhs_xpure = MCP.pure_of_mix lhs_xpure in
    let rhs_xpure = MCP.pure_of_mix rhs_xpure in
    let fml = CP.mkAnd lhs_xpure rhs_xpure pos in
    let check_sat = Omega.is_sat fml "0" in
    let iv = estate.es_infer_vars in
    let invariants = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos) estate.es_infer_invs in
    if check_sat then
(*      let new_p = simplify fml iv in                            *)
(*      let new_p = simplify (CP.mkAnd new_p invariants pos) iv in*)
(*      if CP.isConstTrue new_p then None                         *)
(*      else                                                      *)
        let args = CP.fv fml in
        let quan_var = CP.diff_svl args iv in
(*        let new_p = CP.mkExists_with_simpl_debug Omega.simplify quan_var new_p None pos in*)
        let new_p = Omega.simplify (CP.mkForall quan_var 
          (CP.mkOr (CP.mkNot_s lhs_xpure) rhs_xpure None pos) None pos) in
        let new_p = Omega.simplify (simplify_disjs new_p lhs_xpure rhs_xpure) in
        let args = CP.fv new_p in
        let new_p =
          if CP.intersect args iv == [] then
            let new_p = if CP.isConstFalse new_p then fml else CP.mkAnd fml new_p pos in
            let new_p = simplify new_p iv in
            let new_p = simplify (CP.mkAnd new_p invariants pos) iv in
            let args = CP.fv new_p in
            let quan_var = CP.diff_svl args iv in
            CP.mkExists_with_simpl_debug Omega.simplify quan_var new_p None pos
          else
            simplify new_p iv
        in
        if CP.isConstTrue new_p || CP.isConstFalse new_p then None
        else
          let _,ante_pure,_,_,_ = CF.split_components estate.es_orig_ante in
          let ante_conjs = CP.list_of_conjs (MCP.pure_of_mix ante_pure) in
          let new_p_conjs = CP.list_of_conjs new_p in
          let new_p = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos)
            (List.filter (fun c -> not (is_elem_of c ante_conjs)) new_p_conjs) in
          (* Thai: Should check if the precondition overlaps with the orig ante *)
          (* And simplify the pure in the residue *)
          let new_es_formula = normalize 0 estate.es_formula (CF.formula_of_pure_formula new_p pos) pos in
(*          let h, p, fl, b, t = CF.split_components new_es_formula in                                                 *)
(*          let new_es_formula = Cformula.mkBase h (MCP.mix_of_pure (Omega.simplify (MCP.pure_of_mix p))) t fl b pos in*)
          let args = CP.fv new_p in 
          let new_iv = CP.diff_svl iv args in
          let new_estate =
            {estate with 
                es_formula = new_es_formula;
                (* es_infer_pure = estate.es_infer_pure@[new_p]; *)
                es_infer_vars = new_iv
            }
          in
          Some (new_estate,new_p)
    else
      let check_sat = Omega.is_sat lhs_xpure "0" in
      if not(check_sat) then None
      else      
        let lhs_simplified = simplify lhs_xpure iv in
        let args = CP.fv lhs_simplified in 
        let exists_var = CP.diff_svl args iv in
        let lhs_simplified = CP.mkExists_with_simpl_debug Omega.simplify exists_var lhs_simplified None pos in
        let new_p = simplify_contra (CP.mkAnd (CP.mkNot_s lhs_simplified) invariants pos) iv in
        if CP.isConstFalse new_p then None
        else
(*          let args = CP.fv new_p in *)
          (* let new_iv = (CP.diff_svl iv args) in *)
          let new_estate =
            {estate with 
                es_formula = CF.mkFalse (CF.mkNormalFlow ()) pos;
                es_infer_pure = estate.es_infer_pure@[new_p]
                    (* ;es_infer_vars = new_iv *)
            }
          in
          Some (new_estate,new_p)

let infer_pure_m i estate lhs_xpure rhs_xpure pos =
(* type: Cformula.entail_state ->
  MCP.mix_formula ->
  MCP.mix_formula -> Globals.loc -> Cformula.entail_state option
*)
  let pr1 = !print_mix_formula in 
  let pr2 = !print_entail_state in 
      Gen.Debug.no_3_num i "infer_pure_m" pr2 pr1 pr1 (pr_option (pr_pair pr2 pr_no)) 
      (fun _ _ _ -> infer_pure_m estate lhs_xpure rhs_xpure pos) estate lhs_xpure rhs_xpure   

let infer_empty_rhs estate lhs_p rhs_p pos =
  estate

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

let infer_empty_rhs2 estate lhs_xpure rhs_p pos =
  estate

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
let infer_for_unfold prog estate lhs_node pos =
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
    in {estate with es_infer_invs = inv} 

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
