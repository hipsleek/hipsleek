(*
26.11.2008
todo: disable the default logging for omega
*)

open Globals
open Cast
open Cformula
open Prooftracer
open Gen.Basic

module CP = Cpure
module PR = Cprinter
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher
module Cpr = Cperm
(* globals 4 the immutability extension *)
(* let crt_hole = ref (Globals.fresh_int ());; *)
(* let crt_ctx = ref (Context.mk_empty_frame ());; *)
(* let crt_phase = ref (None);; *)

let count_br_specialized prog cl = 
let helper prog h_node = match h_node with	
	| ViewNode v ->
		Gen.Profiling.inc_counter "consumed_nodes_counter";
		let vdef = look_up_view_def v.h_formula_view_pos prog.prog_view_decls v.h_formula_view_name in
		let i = match v.h_formula_view_remaining_branches with
			| None -> 0
			| Some s -> (List.length vdef.view_prune_branches)-(List.length s) in
		if i>0 then  Gen.Profiling.inc_counter "consumed_specialized_nodes" else ();
    Some h_node
	| _  -> None in
  let f_e_f e = None in
	let f_f e = None in
	let f_h_f e =  helper prog e in
  let f_memo e =  Some e in
  let f_aset e = Some e in
	let f_formula e = Some e in
	let f_b_formula e = Some e in
	let f_exp e = Some e in
    let f_perm e = Some e in 
  (*let f_fail e = e in*)
  let f_ctx e = 
    let f = e.es_formula in
    let _ = transform_formula (f_e_f,f_f,f_h_f,(f_perm,f_perm),(f_memo,f_aset, f_formula, f_b_formula, f_exp)) f in
    Ctx e in
  let _ = transform_context f_ctx cl in
  ()

(*
  - count how many int constants are contained in one expression
  - if there are more than 1 --> means that we can simplify further (by performing the operation)
*)
let variance_graph = ref []
let var_checked_list = ref []

let rec count_iconst (f : CP.exp) = match f with
  | CP.Subtract (e1, e2, _)
  | CP.Add (e1, e2, _) -> ((count_iconst e1) + (count_iconst e2))
  | CP.Mult (e1, e2, _)
  | CP.Div (e1, e2, _) -> ((count_iconst e1) + (count_iconst e2))
  | CP.IConst _ -> 1
  | _ -> 0

let simpl_b_formula (f : CP.b_formula): CP.b_formula =  match f with
  | CP.Lt (e1, e2, pos)
  | CP.Lte (e1, e2, pos)
  | CP.Gt (e1, e2, pos)
  | CP.Gte (e1, e2, pos)
  | CP.Eq (e1, e2, pos)
  | CP.Neq (e1, e2, pos)
  | CP.BagSub (e1, e2, pos) ->
      if ((count_iconst e1) > 1) or ((count_iconst e2) > 1) then
	    (*let _ = print_string("\n[solver.ml]: Formula before simpl: " ^ Cprinter.string_of_b_formula f ^ "\n") in*)
	    let simpl_f = TP.simplify_a 9 (CP.BForm(f,None)) in
  	    begin
  	      match simpl_f with
  	        | CP.BForm(simpl_f1,_) ->
  		        (*let _ = print_string("\n[solver.ml]: Formula after simpl: " ^ Cprinter.string_of_b_formula simpl_f1 ^ "\n") in*)
  		        simpl_f1
  	        | _ -> f
  	    end
      else f
  | CP.EqMax (e1, e2, e3, pos)
  | CP.EqMin (e1, e2, e3, pos) ->
      if ((count_iconst e1) > 1) or ((count_iconst e2) > 1) or ((count_iconst e3) > 1) then
	    (*let _ = print_string("\n[solver.ml]: Formula before simpl: " ^ Cprinter.string_of_b_formula f ^ "\n") in*)
	    let simpl_f = TP.simplify_a 8 (CP.BForm(f,None)) in
  	    begin
  	      match simpl_f with
  	        | CP.BForm(simpl_f1,_) ->
  		        (*let _ = print_string("\n[solver.ml]: Formula after simpl: " ^ Cprinter.string_of_b_formula simpl_f1 ^ "\n") in*)
  		        simpl_f1
  	        | _ -> f
  	    end
      else f
  | CP.BagIn (sv, e1, pos)
  | CP.BagNotIn (sv, e1, pos) ->
      if ((count_iconst e1) > 1) then
	    (*let _ = print_string("\n[solver.ml]: Formula before simpl: " ^ Cprinter.string_of_b_formula f ^ "\n") in*)
	    let simpl_f = TP.simplify_a 7 (CP.BForm(f,None)) in
  	    begin
  	      match simpl_f with
  	        | CP.BForm(simpl_f1,_) ->
  		        (*let _ = print_string("\n[solver.ml]: Formula after simpl: " ^ Cprinter.string_of_b_formula simpl_f1 ^ "\n") in*)
  		        simpl_f1
  	        | _ -> f
  	    end
      else f
  | CP.ListIn (e1, e2, pos)
  | CP.ListNotIn (e1, e2, pos)
  | CP.ListAllN (e1, e2, pos)
  | CP.ListPerm (e1, e2, pos) ->
		if ((count_iconst e1) > 1) or ((count_iconst e2) > 1) then
			(*let _ = print_string("\n[solver.ml]: Formula before simpl: " ^ Cprinter.string_of_b_formula f ^ "\n") in*)
			let simpl_f = TP.simplify_a 6 (CP.BForm(f,None)) in
  		begin
  		match simpl_f with
  		| CP.BForm(simpl_f1,_) ->
  			(*let _ = print_string("\n[solver.ml]: Formula after simpl: " ^ Cprinter.string_of_b_formula simpl_f1 ^ "\n") in*)
  			simpl_f1
  		| _ -> f
  		end
  	else f
 	| _ -> f


let rec filter_formula_memo f (simp_b:bool)=
  match f with
    | Or c -> mkOr (filter_formula_memo c.formula_or_f1 simp_b) (filter_formula_memo c.formula_or_f2 simp_b) no_pos
    | Base b-> 
      let fv = (h_fv b.formula_base_heap)@(MCP.mfv b.formula_base_pure) in
      let nmem = MCP.filter_useless_memo_pure (TP.simplify_a 5) simp_b fv b.formula_base_pure in
      Base {b with formula_base_pure = nmem;}
    | Exists e-> 
      let fv = (h_fv e.formula_exists_heap)@(MCP.mfv e.formula_exists_pure)@e.formula_exists_qvars in
      let nmem = MCP.filter_useless_memo_pure (TP.simplify_a 4) simp_b fv e.formula_exists_pure in
      Exists {e with formula_exists_pure = nmem;}

(* let filter_formula_memo f (simp_b:bool)=  *)
(*   let pr = Cprinter.string_of_formula in *)
(*   Gen.Debug.no_2 "filter_formula_memo"  *)
(*    pr string_of_bool pr *)
(*    (fun _ _ -> filter_formula_memo f simp_b) f simp_b *)

(*find what conditions are required in order for the antecedent node to be pruned sufficiently
  to match the conseq, if the conditions relate only to universal variables then move them to the right*)
let prune_branches_subsume_x prog lhs_node rhs_node :(bool*(CP.formula*bool) option)= match lhs_node,rhs_node with
  | DataNode dn1, DataNode dn2-> 
    (match (dn1.h_formula_data_remaining_branches,dn2.h_formula_data_remaining_branches) with
      | None,None -> (true, None)
      | Some l1, _ -> (true, None) (*(Gen.BList.subset_eq (=) l1 l2, None)*)
      | None, Some _ -> 
        Debug.print_info "Warning: " "left hand side node is not specialized!" no_pos;
        (false, None))
  | ViewNode vn1, ViewNode vn2->
    (match (vn1.h_formula_view_remaining_branches,vn2.h_formula_view_remaining_branches) with
      | None,None -> (true, None)
      | Some l1, Some l2 -> 
		let need_prunning = Gen.BList.difference_eq (=) l1 l2 in		
		if (List.length need_prunning)<=0 then (true,None) (**)
		else
          let v_def = look_up_view_def no_pos prog.prog_view_decls vn2.h_formula_view_name in
          let to_vars = vn2.h_formula_view_node:: vn2.h_formula_view_arguments in
          let self_v = CP.SpecVar (Named v_def.view_data_name, self, if (CP.is_primed vn2.h_formula_view_node) then Primed else Unprimed) in
          let from_vars = self_v::v_def.view_vars in
          let subst_vars = List.combine from_vars to_vars in
          let new_cond = List.map (fun (c1,c2)-> (CP.b_subst subst_vars c1,c2)) v_def.view_prune_conditions in         
          let new_cond = List.filter (fun (_,c2)-> (List.length (Gen.BList.intersect_eq (=) need_prunning c2))>0) new_cond in
          if (Gen.BList.subset_eq (=) need_prunning (List.concat (List.map snd new_cond))) then 
			(*i have enough prunning conditions to succeed*)
            let ll = List.map (fun c -> List.filter (fun (_,c1)-> List.exists ((=) c) c1) new_cond) need_prunning in (*posib prunning cond for each branch*)
            let wrap_f (c,_) = CP.BForm ((MCP.memo_f_neg c),None) in
            let ll = List.map (fun l -> List.fold_left (fun a c-> CP.mkOr a (wrap_f c) None no_pos) (wrap_f (List.hd l)) (List.tl l)) ll in
            let inst_forms = CP.conj_of_list ll no_pos in
            (*let inst_forms = CP.conj_of_list (List.map (fun (c,_)-> CP.BForm ((MCP.memo_f_neg c),None)) new_cond) no_pos in*)
			let fls = ((List.length need_prunning)=(List.length l1)) in
            (true, Some (inst_forms,fls))
          else (print_string "I do not have enough prunning conditions to succeed in this match\n";(false, None)) (*this should not occur though*)
      | None, Some _ ->
        Debug.print_info "Warning: " "left hand side node is not specialized!" no_pos;
        (false, None)
      | Some _, None ->
        Debug.print_info "Warning: " "right hand side node is not specialized!" no_pos;
        (true, None)
      )
  | _ -> (false, None)      

let prune_branches_subsume prog lhs_node rhs_node = 
  let pr1 = pr_pair Cprinter.string_of_pure_formula string_of_bool in
  let pr2 (c,d)= Cprinter.pr_pair string_of_bool (Cprinter.pr_opt pr1) in
  let pr = Cprinter.string_of_h_formula in
  Gen.Debug.no_2 "pr_branches_subsume " pr pr pr2 (fun _ _ -> prune_branches_subsume_x prog lhs_node rhs_node) lhs_node rhs_node

  
let heap_entail_agressive_prunning (crt_heap_entailer:'a -> 'b) (prune_fct:'a -> 'a) (res_checker:'b-> bool) (argument:'a) :'b =
  begin
   Globals.prune_with_slice := !Globals.enable_aggressive_prune;
   let first_res = crt_heap_entailer argument in
   first_res (*
   let res = match !Globals.enable_aggressive_prune, !Globals.disable_aggressive_prune with
      | true, true 
      | false, false -> 
        if (res_checker first_res) then first_res
        else 
        (Globals.prune_with_slice := true;
         let r = prune_fct argument in
         crt_heap_entailer r
         )
      | false, true 
      | true , false ->  first_res in
   Globals.prune_with_slice := false; 
   res
   *)
  end
  
let clear_entailment_history_es (es :entail_state) :context = 
  Ctx {(empty_es (mkTrueFlow ()) no_pos) with 
    es_formula = filter_formula_memo es.es_formula false;
	es_path_label = es.es_path_label;
	es_prior_steps= es.es_prior_steps;
	es_var_measures = es.es_var_measures;
	es_var_label = es.es_var_label} 

let clear_entailment_history (ctx : context) : context =  
  transform_context clear_entailment_history_es ctx

let clear_entailment_history_list (ctx : list_context) : list_context = 
  transform_list_context (clear_entailment_history_es,(fun c->c)) ctx 

let clear_entailment_history_partial_list (ctx : list_partial_context) : list_partial_context = 
  transform_list_partial_context (clear_entailment_history_es,(fun c->c)) ctx 

let fail_ctx_stk = ref ([]:fail_type list)
let previous_failure () = not(Gen.is_empty !fail_ctx_stk)


(* let enable_distribution = ref true *)
let imp_no = ref 1

class entailhist =
object (self)
  val en_hist = Hashtbl.create 40

  method init () = Hashtbl.clear en_hist

  method upd_opt (pid : control_path_id) (rs: list_context) (errmsg: string) =
    match pid with 
	None -> failwith errmsg;
      | Some (pid_i,_) -> Hashtbl.add en_hist pid_i rs

  method upd (pid : formula_label) (rs: list_context) =
    let pid_i,_ = pid in
      Hashtbl.add en_hist pid_i rs

  method get (id : int) : list_context list =
    Hashtbl.find_all en_hist id

end

let entail_hist = new entailhist 

let no_diff = ref false (* if true, then xpure_symbolic will drop the disequality generated by * *)

let no_check_outer_vars = ref false 

(*----------------*)
let rec formula_2_mem_x (f : CF.formula) prog : CF.mem_formula = 
  (* for formula *)	
  (* let _ = print_string("f = " ^ (Cprinter.string_of_formula f) ^ "\n") in *)
  let rec helper f =
    match f with
      | Base ({ formula_base_heap = h;
                formula_base_perm = pr}) -> 
          let pr_sol = Cpr.solve_once pr in
	        h_formula_2_mem h [] pr_sol prog
      | Exists ({formula_exists_qvars = qvars;
                 formula_exists_heap = qh;
                 formula_exists_perm = pr;}) ->
          let pr_sol = Cpr.solve_once pr in
	        h_formula_2_mem qh qvars pr_sol prog
      | Or ({ formula_or_f1 = f1;
              formula_or_f2 = f2}) ->
	        let m1 = helper f1  in
	        let m2 = helper f2  in 
	        {mem_formula_mset = (CP.DisjSetSV.or_disj_set m1.mem_formula_mset m2.mem_formula_mset)}
  in helper f

and formula_2_mem (f : formula) prog : CF.mem_formula = 
  Gen.Debug.no_1 "formula_2_mem" Cprinter.string_of_formula Cprinter.string_of_mem_formula
      (fun _ -> formula_2_mem_x f prog) f

and h_formula_2_mem_debug (f : h_formula) (evars : CP.spec_var list) pr prog : CF.mem_formula = 
  Gen.Debug.no_1 "h_formula_2_mem" Cprinter.string_of_h_formula Cprinter.string_of_mem_formula
      (fun f -> h_formula_2_mem f evars pr prog) f

and h_formula_2_mem (f : h_formula) (evars : CP.spec_var list) pr_sol prog : CF.mem_formula = 
  let rec helper f =
    (* for h_formula *)
    match f with
      | Star ({h_formula_star_h1 = h1;
	    h_formula_star_h2 = h2;
	    h_formula_star_pos = pos}) -> 
	        let m1 = helper h1  in
	        let m2 = helper h2 in
	        let m = (CP.DisjSetSV.star_disj_set m1.mem_formula_mset m2.mem_formula_mset) in
	        let res = {mem_formula_mset = m;} in
	        res
      | Phase ({h_formula_phase_rd = h1;
	    h_formula_phase_rw = h2;
	    h_formula_phase_pos = pos})  
      | Conj ({h_formula_conj_h1 = h1;
	    h_formula_conj_h2 = h2;
	    h_formula_conj_pos = pos}) ->
	        let m1 = helper h1 in
	        let m2 = helper h2 in
	        let m = (CP.DisjSetSV.merge_disj_set m1.mem_formula_mset m2.mem_formula_mset) in
	        {mem_formula_mset = m;}
      | DataNode ({
          h_formula_data_node = p;
          h_formula_data_perm = pr;
          h_formula_data_pos = pos}) ->
	        let new_mset = 
	          if List.mem p evars then CP.DisjSetSV.mkEmpty
	          else CP.DisjSetSV.singleton_dset (Cpr.var_2_prop_var pr_sol p pr) in
	        {mem_formula_mset = new_mset;}
      | ViewNode ({ h_formula_view_node = p;
        h_formula_view_name = c;
        h_formula_view_arguments = vs;
        h_formula_view_remaining_branches = lbl_lst;
        h_formula_view_perm = pr;
        h_formula_view_pos = pos}) ->
            let vdef = look_up_view_def pos prog.prog_view_decls c in
            let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
            let vs  = Cpr.var_2_prop_var_list pr_sol vs pr in
            let np  = Cpr.var_2_prop_var pr_sol p pr in
            let to_svs = np :: vs in
 	        let new_mset = 
              (match lbl_lst with
                |None ->
                      if List.mem p evars then CP.BagaSV.mkEmpty
	                    else look_up_view_baga prog c np vs 
                | Some ls -> 
                   lookup_view_baga_with_subs ls vdef from_svs to_svs) in
	        {mem_formula_mset = CP.DisjSetSV.one_list_dset new_mset;} 
      | Hole _
      | HTrue
      | HFalse ->
         (*  let _ = print_endline "h_formula_2_mem: HTrue, HFalse, Hole" in*)
         {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
  in helper f

let rec xpure (prog : prog_decl) (f0 : formula) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga * CF.mem_formula) =
  (* print_string "calling xpure"; *)
  if (!Globals.allow_imm) then xpure_symbolic prog f0
  else xpure_symbolic prog f0
    (*let a, b, c = xpure_mem_enum prog f0 in
    (a, b, [], c)*)

and xpure_heap i (prog : prog_decl) (h0 : h_formula) (which_xpure :int) p pr
  : (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga* CF.mem_formula)= 
  Gen.Debug.no_2_num i "xpure_heap" Cprinter.string_of_h_formula string_of_int 
  (fun (mf,_,_,m) -> pr_pair Cprinter.string_of_mix_formula Cprinter.string_of_mem_formula (mf,m)) 
  (fun _ _ -> xpure_heap_x prog h0 which_xpure p pr) h0 which_xpure

and xpure_heap_x (prog : prog_decl) (h0 : h_formula) (which_xpure :int) p pr
  : (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga * CF.mem_formula) =
   if (!Globals.allow_imm) then xpure_heap_symbolic prog h0 which_xpure p pr
  else xpure_heap_symbolic prog h0 which_xpure p pr
    (*let a, b, c = xpure_heap_symbolic prog h0 which_xpure p pr in
    (a, b, [], c)*)

(* TODO : if no complex & --eps then then return true else xpure1 generated;
   what if user invariant has a disjunct? *)
(*
and xpure_mem_enum (prog : prog_decl) (f0 : formula) : (MCP.mix_formula * (branch_label * CP.formula) list * CF.mem_formula) = 
  Gen.Debug.no_1 "xpure_mem_enum" Cprinter.string_of_formula (fun (a1,_,a3)->(Cprinter.string_of_mix_formula a1)^"#"
      ^(Cprinter.string_of_mem_formula a3)) (fun f0 -> xpure_mem_enum_x prog f0) f0


(* xpure approximation with memory enumeration *)
and xpure_mem_enum_x (prog : prog_decl) (f0 : formula) : (MCP.mix_formula * (branch_label * CP.formula) list * CF.mem_formula) = 
  let mset = formula_2_mem f0 prog in 
  let rec xpure_helper  (prog : prog_decl) (f0 : formula) : (MCP.mix_formula * (branch_label * CP.formula) list) = 
    match f0 with
      | Or ({ formula_or_f1 = f1;
	    formula_or_f2 = f2;
	    formula_or_pos = pos}) ->
            let pf1, pf1b = xpure_helper prog f1 in
            let pf2, pf2b = xpure_helper prog f2 in
            let br = CP.or_branches pf1b pf2b in
		    (* let branches = Gen.BList.remove_dups_eq (=) (fst (List.split pf1b) @ (fst (List.split pf2b))) in *)
		    (* let map_fun branch = *)
		    (*   try  *)
		    (*     let l1 = List.assoc branch pf1b in *)
		    (*     try *)
		    (*       let l2 = List.assoc branch pf2b in *)
		    (*       CP.mkOr l1 l2 None pos *)
		    (*     with Not_found -> CP.mkTrue no_pos *)
		    (*   with Not_found -> CP.mkTrue no_pos *)
		    (* in *)
		    (* let map_fun b = (b, map_fun b) in *)
		    (* let br = (List.map map_fun branches) in *)
	        (MCP.mkOr_mems pf1 pf2 ), br

      | Base ({ formula_base_heap = h;
		formula_base_pure = p;
		formula_base_branches = br;
    formula_base_perm = pr;
		formula_base_pos = pos}) ->
            let pr_sol = Cpr.solve_once pr in
            let (ph, phb, _) = xpure_heap_mem_enum prog h 1 p pr_sol in
            let n_p = MCP.merge_mems p ph true in           
            let cf = (MCP.fold_mem_lst (CP.mkTrue no_pos) false true n_p) in
            let rb = CP.merge_branches_with_common br phb cf [] in   
            (* let phb = CP.merge_branches phb br in *)
            (* let rb = if (List.length phb) = 0 then [] *)
            (* else *)
            (*   let r = MCP.fold_mem_lst (CP.mkTrue pos) false true n_p in *)
            (*   (\* let r = MCP.fold_mem_lst (MCP.fold_mem_lst (CP.mkTrue pos) false true ph) false true p in *\) *)
            (*   List.map (fun (l, x) -> (l, CP.mkAnd x r pos)) phb in *)
            (n_p,rb)
      | Exists ({ formula_exists_qvars = qvars;
		formula_exists_heap = qh;
		formula_exists_pure = qp;
		formula_exists_branches = br;
    formula_exists_perm = pr;
		formula_exists_pos = pos}) ->
            let pr_sol = Cpr.solve_once pr in
            let (pqh, pqhb, _) = xpure_heap_mem_enum prog qh 1 qp pr_sol in
            (*let pqhb = CP.merge_branches pqhb br in
              let sqvars = (* List.map CP.to_int_var *) qvars in*)
            let tmp1 = MCP.merge_mems qp pqh true in
            let cf2 = MCP.memo_pure_push_exists qvars tmp1 in
            let cf = (MCP.fold_mem_lst (CP.mkTrue no_pos) false true tmp1) in
            let rb = CP.merge_branches_with_common pqhb br cf qvars in
		    (* let rb = if (List.length pqhb)=0 then [] *)
		    (* else *)
		    (*   let r = MCP.fold_mem_lst (MCP.fold_mem_lst (CP.mkTrue pos) false true pqh) false true qp in *)
		    (*   let wrap_exists f = List.fold_left (fun f -> fun qv -> CP.Exists (qv, f, None, pos)) f sqvars in *)
		    (*   (List.map (fun (l, x) -> (l, wrap_exists (CP.mkAnd x r pos))) pqhb) in *)
	        (cf2, rb)
  in 
  let pf, pb = xpure_helper prog f0 in
  (pf, pb, mset)


and xpure_heap_mem_enum(*_debug*) (prog : prog_decl) (h0 : h_formula) (which_xpure :int) p pr:
  (MCP.mix_formula * (branch_label * CP.formula) list * CF.mem_formula) =  
  Gen.Debug.ho_2 "xpure_heap_mem_enum" Cprinter.string_of_h_formula string_of_int (fun (a1,_,a3)->(Cprinter.string_of_mix_formula a1)^"#"
    ^(Cprinter.string_of_mem_formula a3)) (fun _ _ -> xpure_heap_mem_enum_x prog h0 which_xpure p pr) h0 which_xpure 


and xpure_heap_mem_enum_x (prog : prog_decl) (h0 : h_formula) (which_xpure :int) p pr : (MCP.mix_formula * (branch_label * CP.formula) list * CF.mem_formula) =
  (* let _  = print_string("Calling xpure_heap for f = " ^ (Cprinter.string_of_h_formula h0) ^ "\n") in *)
  if not (is_h_normalized h0 p) then report_error no_pos "xpure_heap_mem_enum: xpuring a non normalized formula"
  else
  let memset = h_formula_2_mem h0 [] pr prog in

  let rec xpure_heap_helper (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list) = 
    match h0 with
      | DataNode ({h_formula_data_node = p;
                   h_formula_data_pos = pos}) ->
            let i = fresh_int2 () in
            let non_null = CP.mkEqVarInt p i pos in
	        (MCP.memoise_add_pure_N (MCP.mkMTrue pos) non_null , [])
      | ViewNode ({ h_formula_view_node = p;
		h_formula_view_name = c;
		h_formula_view_arguments = vs;
		h_formula_view_remaining_branches = rm_br;
		h_formula_view_pos = pos}) ->
            let vdef = look_up_view_def pos prog.prog_view_decls c in
            let rec helper addrs =
	          match addrs with
	            | a :: rest ->
	                  let i = fresh_int () in
	                  let non_null = CP.mkEqVarInt a i pos in
	                  let rest_f = helper rest in
	                  let res_form = CP.mkAnd non_null rest_f pos in
	                  res_form
	            | [] -> CP.mkTrue pos in
            let inv_opt =  Cast.get_xpure_one vdef rm_br in
            (* match rm_br with *)
            (*               | Some l -> let n=(List.length l) in   *)
            (*                 if n<(List.length vdef.view_prune_branches) then None *)
            (*                 else (match vdef.view_complex_inv with  *)
            (*                   | None -> None  *)
            (*                   | Some f -> Some f)  (\* unspecialised with a complex_inv *\) *)
            (*               | None -> Some vdef.view_x_formula  *)
            (* in *)
            (match inv_opt with
              | None -> (MCP.mkMTrue no_pos, [])
              | Some xp1 ->
                    let vinv = match which_xpure with
                      | -1 -> (MCP.mkMTrue no_pos, [])
                      | 0 -> vdef.view_user_inv
                      | _ -> xp1 in
                    let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
                    let to_svs = p :: vs in
                    let (f, b) = vinv in
                    let subst_m_fun = MCP.subst_avoid_capture_memo(*_debug1*) from_svs to_svs in
                    let subst_fun = CP.subst_avoid_capture from_svs to_svs in
                    let tmp1 = subst_m_fun f, List.map (fun (x,y) -> x, subst_fun y) b in
                    tmp1)
      | Star ({h_formula_star_h1 = h1;
	    h_formula_star_h2 = h2;
	    h_formula_star_pos = pos})
      | Phase ({h_formula_phase_rd = h1;
		h_formula_phase_rw = h2;
		h_formula_phase_pos = pos})
      | Conj ({h_formula_conj_h1 = h1;
	    h_formula_conj_h2 = h2;
	    h_formula_conj_pos = pos}) ->
            let (ph1, ph1b) = xpure_heap_helper prog h1 which_xpure in
            let (ph2, ph2b) = xpure_heap_helper prog h2 which_xpure in
            let res_form = (MCP.merge_mems ph1 ph2 true, CP.merge_branches ph1b ph2b) in
	        res_form
      | HTrue  -> (MCP.mkMTrue no_pos, [])
      | HFalse -> (MCP.mkMFalse no_pos, [])
      | Hole _ -> (MCP.mkMTrue no_pos, []) (*report_error no_pos "[solver.ml]: An immutability marker was encountered in the formula\n"*)
  in
  let ph, pb = xpure_heap_helper prog h0 which_xpure in
  if (is_sat_mem_formula memset) then 
    (ph, pb,  memset)
  else (MCP.mkMFalse no_pos, pb, memset)  
*)
and xpure_symbolic_debug (prog : prog_decl) (h0 : formula) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga * CF.mem_formula) = 
  Gen.Debug.no_1 "xpure_symbolic" Cprinter.string_of_formula 
      (fun (p1,_,vl,p4) -> (Cprinter.string_of_mix_formula p1)^"#"^(Cprinter.string_of_spec_var_list vl)^"#
"^(Cprinter.string_of_mem_formula p4)) (* (fun (p1,_,_,p4) -> not(is_sat_mem_formula p4)) *)
      (fun h0 -> xpure_symbolic prog h0) h0

(* xpure approximation without memory enumeration *)
and xpure_symbolic (prog : prog_decl) (f0 : formula) : 
      (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga * CF.mem_formula) = 
  let mset = formula_2_mem f0 prog in 
  let rec xpure_symbolic_helper (prog : prog_decl) (f0 : formula) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga) = match f0 with
    | Or ({ formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos}) ->
          let ipf1, pf1b, avars1 = xpure_symbolic_helper prog f1 in
          let ipf2, pf2b, avars2 = xpure_symbolic_helper prog f2 in
          let br = CP.or_branches pf1b pf2b in
          (* let branches = Gen.BList.remove_dups_eq (=) (fst (List.split pf1b) @ (fst (List.split pf2b))) in *)
          (* let map_fun branch = *)
          (*   try  *)
          (*     let l1 = List.assoc branch pf1b in *)
          (*       try *)
          (*         let l2 = List.assoc branch pf2b in *)
	      (*   CP.mkOr l1 l2 None pos *)
          (*       with Not_found -> CP.mkTrue pos *)
          (*   with Not_found -> CP.mkTrue pos *)
          (* in *)
          (* let map_fun b = (b, map_fun b) in *)
          (* let br = (List.map map_fun branches) in *)
          let res_form = MCP.mkOr_mems ipf1 ipf2  in
          (res_form, br, CP.BagaSV.intersect avars1 avars2)
    | Base ({ formula_base_heap = h;
	  formula_base_pure = p;
	  formula_base_branches = fbr;
    formula_base_perm = pr;
	  formula_base_pos = pos}) ->
          let pr_sol = Cpr.solve_once pr in
          let ph, br, addrs, _ = xpure_heap_symbolic prog h 1 p pr_sol in
          let n_p = MCP.merge_mems p ph true in
          let cf = (MCP.fold_mem_lst (CP.mkTrue no_pos) false true n_p) in
          (* let n_br = CP.merge_branches br fbr in       *)
          let rb = CP.merge_branches_with_common br fbr cf [] in   
          (* let r_br = if (List.length n_br)=0 then [] *)
          (* else *)
          (*   let res_form = MCP.fold_mem_lst (MCP.fold_mem_lst (CP.mkTrue no_pos) false true ph) false true p in *)
          (*   List.map (fun (l, x) -> (l, CP.mkAnd x res_form pos)) n_br in *)
          (n_p, rb, addrs)
    | Exists ({ formula_exists_qvars = qvars;
	  formula_exists_heap = qh;
	  formula_exists_pure = qp;
	  formula_exists_branches = fbr;
    formula_exists_perm = pr;
	  formula_exists_pos = pos}) ->
          let pr_sol = Cpr.solve_once pr in
          let pqh, br, addrs', _ = xpure_heap_symbolic prog qh 1 qp pr_sol in
          let sqvars = (* List.map CP.to_int_var *) qvars in
          let addrs = Gen.BList.difference_eq (fun a b -> CP.eq_spec_var (fst a) b)addrs' sqvars in
          let tmp1 = MCP.merge_mems qp pqh true in
          let res_form = MCP.memo_pure_push_exists sqvars tmp1 in
          let cf = (MCP.fold_mem_lst (CP.mkTrue no_pos) false true tmp1) in
          (* let n_br = CP.merge_branches br fbr in  *)     
          let rb = CP.merge_branches_with_common br fbr cf sqvars in   
          (* let wrap_exists f = *)
          (*   let fv = CP.fv f in *)
          (*   let sqvars = List.filter (fun sv -> List.mem sv fv) sqvars in *)
          (*   List.fold_left (fun f -> fun qv -> CP.Exists (qv, f, None, pos)) f sqvars *)
          (* in *)
          (* let rb = if (List.length n_br)=0 then [] *)
          (* else  *)
          (*   let r = MCP.fold_mem_lst (MCP.fold_mem_lst (CP.mkTrue no_pos) false true pqh) false true qp in *)
          (*   List.map (fun (l, x) -> (l, wrap_exists (CP.mkAnd x r pos))) n_br in *)
          (res_form, rb, addrs)
  in 
  let pf, pb, pa = xpure_symbolic_helper prog f0 in
  (pf, pb, pa, mset)


and xpure_heap_symbolic(*_debug*) (prog : prog_decl) (h0 : h_formula) (which_xpure :int) p pr 
  : (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga * CF.mem_formula) = 
  Gen.Debug.no_1_opt 
      (fun (p1,_,_,p4) -> not(is_sat_mem_formula p4)) 
      "xpure_heap_symbolic" Cprinter.string_of_h_formula 
      (fun (p1,_,p3,p4) -> (Cprinter.string_of_mix_formula p1)^"#"^(string_of_spec_var_list p3)^"#"^(Cprinter.string_of_mem_formula p4)
          ^string_of_bool(is_sat_mem_formula p4)) 
      (fun h0 -> xpure_heap_symbolic_x prog h0 which_xpure p pr) h0

and xpure_heap_symbolic_x (prog : prog_decl) (h0 : h_formula) (which_xpure :int) p pr
  : (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga * CF.mem_formula) = 
  let memset = h_formula_2_mem h0 [] pr prog in
  let ph, pb, pa = xpure_heap_symbolic_i prog h0 which_xpure p pr in
  if (is_sat_mem_formula memset)then (ph, pb, pa, memset)
  else (MCP.mkMFalse no_pos, pb, pa, memset)  


and heap_baga (prog : prog_decl) (h0 : h_formula) pr_sol: P.BagaSV.baga = 
  let rec helper h0 = match h0 with
    | DataNode ({ h_formula_data_node = p;h_formula_data_perm = pr;}) ->[Cpr.var_2_prop_var pr_sol p pr]
    | ViewNode ({ h_formula_view_node = p;
      h_formula_view_name = c;
      h_formula_view_arguments = vs;
      h_formula_view_remaining_branches = lbl_lst;
      h_formula_view_perm = pr;
      h_formula_view_pos = pos}) ->
        let p = Cpr.var_2_prop_var pr_sol p pr in
        let vs = Cpr.var_2_prop_var_list pr_sol vs pr in
          (match lbl_lst with
            | None -> look_up_view_baga prog c p vs
            | Some ls ->  
                  let vdef = look_up_view_def pos prog.prog_view_decls c in
                  let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
                  let to_svs = p :: vs in
                  lookup_view_baga_with_subs ls vdef from_svs to_svs )
    | Star ({ h_formula_star_h1 = h1;h_formula_star_h2 = h2}) -> CP.BagaSV.star_union (helper h1) (helper h2)
    | Phase ({ h_formula_phase_rd = h1;h_formula_phase_rw = h2;}) 
    | Conj ({ h_formula_conj_h1 = h1;h_formula_conj_h2 = h2;}) -> CP.BagaSV.and_union (helper h1) (helper h2)
    | HTrue | Hole _ | HFalse -> [] in
  helper h0

and xpure_heap_symbolic_i (prog : prog_decl) (h0 : h_formula) i p prf: (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga) = 
  let pr (mf,bl,_) = pr_pair Cprinter.string_of_mix_formula (pr_list (fun (_,f) -> Cprinter.string_of_pure_formula f)) (mf,bl) in
  Gen.Debug.no_1 "xpure_heap_symbolic_i" Cprinter.string_of_h_formula pr
      (fun h0 -> xpure_heap_symbolic_i_x prog h0 i p prf) h0

and xpure_heap_symbolic_i_x (prog : prog_decl) (h0 : h_formula) xp_no p pr_sol: (MCP.mix_formula * (branch_label * CP.formula) list * CP.BagaSV.baga) = 
  (*if not (is_h_normalized h0 p) then report_error no_pos "xpure_heap_symbolic_i: xpuring a non normalized formula"
  else*)
  let rec helper h0 = match h0 with
    | DataNode ({ h_formula_data_node = p;
	  h_formula_data_label = lbl;
    h_formula_data_perm = pr;
	  h_formula_data_pos = pos}) ->
          let non_zero = CP.BForm (CP.Neq (CP.Var (p, pos), CP.Null pos, pos),lbl) in
          (MCP.memoise_add_pure_N (MCP.mkMTrue pos) non_zero , [], [Cpr.var_2_prop_var pr_sol p pr])
    | ViewNode ({ h_formula_view_node = p;
	  h_formula_view_name = c;
	  h_formula_view_arguments = vs;
	  h_formula_view_remaining_branches = lbl_lst;
    h_formula_view_perm = pr;
	  h_formula_view_pos = pos}) ->
          (* let _ = print_endline ("xpure_heap_symxbolic_i: ViewNode") in*)
          
          let vdef = look_up_view_def pos prog.prog_view_decls c in
          let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
          let to_svs = p :: vs in
          let nvs = Cpr.var_2_prop_var_list pr_sol vs pr in
          let np = Cpr.var_2_prop_var pr_sol p pr in
          let nto_svs = np::nvs in
          (match lbl_lst with
            | None -> 
                  let vinv, vinv_b = if (xp_no=1) then vdef.view_x_formula else vdef.view_user_inv in       
                  let from_addrs = vdef.view_addr_vars in
                  let to_addrs = CP.fresh_spec_vars from_addrs in
                  let subst_m_fun f =
                    let tmp1 = MCP.subst_avoid_capture_memo(*_debug2*) from_svs to_svs f in
                    MCP.memo_subst (List.combine from_addrs to_addrs) tmp1 (* no capture can happen *) in
                  let subst_fun f =
                    let tmp1 = CP.subst_avoid_capture from_svs to_svs f in
                    CP.subst (List.combine from_addrs to_addrs) tmp1 (* no capture can happen *) in
                  (* let _ = print_endline ("xpure_heap_symxbolic_i NONE: svl = " ^ (Cprinter.string_of_spec_var_list ba)) in *)
                  let ba = look_up_view_baga prog c np nvs in
                  (subst_m_fun vinv, List.map (fun (l,x) -> (l, subst_fun x)) vinv_b, ba (*to_addrs*)) 
            | Some ls ->  
                  let ba = lookup_view_baga_with_subs ls vdef from_svs nto_svs in
			      (* let _ = print_endline ("xpure_heap_symxbolic_i SOME: svl = " ^ (Cprinter.string_of_spec_var_list ba)) in*)
                  (MCP.mkMTrue no_pos, [], ba))
    | Star ({ h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
          (* let _ = print_endline ("xpure_heap_symxbolic_i: Star") in*)
          let ph1, b1, addrs1 = helper h1 in
          let ph2, b2, addrs2 = helper h2 in
          (* let all_diff = *)
          (* 	if !no_diff then P.mkTrue no_pos *)
          (* 	else pairwise_diff addrs1 addrs2 pos in *)
          let tmp1 = MCP.merge_mems ph1 ph2 true in
          (* let res_form = MCP.memoise_add_pure_N tmp1 all_diff in *)
          (tmp1, CP.merge_branches b1 b2, CP.BagaSV.star_union  addrs1 addrs2)
    | Phase ({ h_formula_phase_rd = h1;
	  h_formula_phase_rw = h2;
	  h_formula_phase_pos = pos}) 
    | Conj ({ h_formula_conj_h1 = h1;
	  h_formula_conj_h2 = h2;
	  h_formula_conj_pos = pos}) ->
          let ph1, b1, addrs1 = helper h1 in
          let ph2, b2, addrs2 = helper h2 in
          (*let all_diff =
	        if !no_diff then P.mkTrue no_pos
	        else pairwise_diff addrs1 addrs2 pos in*)
          let tmp1 = MCP.merge_mems ph1 ph2 true in
          (*let res_form = MCP.memoise_add_pure_N tmp1 all_diff in*)
          (tmp1, CP.merge_branches b1 b2, CP.BagaSV.and_union addrs1 addrs2)	      
    | HTrue -> (MCP.mkMTrue no_pos, [], [])
    | Hole _ -> (MCP.mkMTrue no_pos, [], []) (* shouldn't get here *)
    | HFalse -> (MCP.mkMFalse no_pos, [], []) in
  helper h0

(* xpure of consumed precondition *)
and xpure_consumed_pre (prog : prog_decl) (f0 : formula) : (CP.formula * (branch_label * CP.formula) list) = match f0 with
  | Or ({ formula_or_f1 = f1;
	formula_or_f2 = f2;
	formula_or_pos = pos}) ->
        let ipf1, pf1b = xpure_consumed_pre prog f1 in
        let ipf2, pf2b = xpure_consumed_pre prog f2 in
        let br = CP.or_branches pf1b pf2b in
        (* let branches = Gen.BList.remove_dups_eq (=) (fst (List.split pf1b) @ (fst (List.split pf2b))) in *)
        (* let map_fun branch = *)
        (*   try  *)
        (*     let l1 = List.assoc branch pf1b in *)
        (*       try *)
        (*         let l2 = List.assoc branch pf2b in *)
	    (*   CP.mkOr l1 l2 None pos *)
        (*       with Not_found -> CP.mkTrue no_pos *)
        (*   with Not_found -> CP.mkTrue no_pos *)
        (* in *)
        (* let map_fun b = (b, map_fun b) in *)
        (* let br = (List.map map_fun branches) in *)
        (CP.mkOr ipf1 ipf2 None pos), br
  | Base ({formula_base_heap = h; formula_base_pos = pos;}) ->
        let (ph, phb) = xpure_consumed_pre_heap prog h in
        (ph, (List.map (fun (l, x) -> (l, CP.mkAnd x ph pos)) phb))
  | Exists ({formula_exists_qvars = qvars;
	formula_exists_heap = qh;
	formula_exists_pure = qp;
	formula_exists_pos = pos}) ->
        let (pqh, pqhb) = xpure_consumed_pre_heap prog qh in
        let res_form = CP.mkExists qvars pqh None pos in
        (pqh, (List.map (fun (l, x) -> (l, CP.mkAnd x res_form pos)) pqhb))

and xpure_consumed_pre_heap (prog : prog_decl) (h0 : h_formula) : (CP.formula * (branch_label * CP.formula) list) = match h0 with
  | DataNode ({h_formula_data_node = p;
	h_formula_data_pos = pos}) -> (CP.mkTrue pos, [])
  | ViewNode ({ h_formula_view_node = p;
	h_formula_view_name = c;
	h_formula_view_arguments = vs;
	h_formula_view_pos = pos}) ->
        let vdef = look_up_view_def pos prog.prog_view_decls c in
        let vinv, vinv_b = vdef.view_user_inv in (* views have been ordered such that this dependency is respected *)
        let vinv = MCP.fold_mem_lst (CP.mkTrue no_pos) false true vinv in
        let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
        let to_svs = p :: vs in
        let tmp1 = CP.subst_avoid_capture from_svs to_svs vinv in
        let tmp1b = List.map (fun (l,f) -> (l, CP.subst_avoid_capture from_svs to_svs f)) vinv_b in
        tmp1, tmp1b
  | Conj ({ h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;
	h_formula_conj_pos = pos}) 
  | Phase ({ h_formula_phase_rd = h1;
	h_formula_phase_rw = h2;
	h_formula_phase_pos = pos}) 
  | Star ({ h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos}) ->
        let (ph1, ph1b) = xpure_consumed_pre_heap prog h1 in
        let (ph2, ph2b) = xpure_consumed_pre_heap prog h2 in
        let tmp1 = (CP.mkAnd ph1 ph2 pos, CP.merge_branches ph1b ph2b) in
        tmp1
  | HTrue -> (P.mkTrue no_pos, [])
  | HFalse -> (P.mkFalse no_pos, [])
  | Hole _ -> (P.mkTrue no_pos, []) (* report_error no_pos ("[solver.ml]: Immutability annotation encountered\n") *)

and pairwise_diff (svars10: P.spec_var list ) (svars20:P.spec_var list) pos =
  let rec diff_one sv svars = match svars with
    | sv2 :: rest ->
          let tmp1 = diff_one sv rest in
          let tmp2 = CP.mkNeqVar sv sv2 pos in
          let res = CP.mkAnd tmp1 tmp2 pos in
          res
    | [] -> CP.mkTrue pos
  in
  if Gen.is_empty svars20 then
    CP.mkTrue pos
  else
    match svars10 with
      | sv :: rest ->
	        let tmp1 = pairwise_diff rest svars20 pos in
	        let tmp2 = diff_one sv svars20 in
	        let res = CP.mkAnd tmp1 tmp2 pos in
	        res
      | [] -> CP.mkTrue pos

and prune_ctx prog ctx = match ctx with
  | OCtx (c1,c2)-> mkOCtx (prune_ctx prog c1) (prune_ctx prog c2) no_pos
  | Ctx es -> Ctx {es with es_formula = prune_preds prog false es.es_formula}

and normalize_frac_ctx prog ctx = match ctx with
  | OCtx (c1,c2)-> mkOCtx (normalize_frac_ctx prog c1) (normalize_frac_ctx prog c2) no_pos
  | Ctx es -> Ctx {es with es_formula = normalize_frac_formula prog es.es_formula}
  
and prune_branch_ctx prog (pt,bctx) = 
  let r = prune_ctx prog bctx in
  let _ = count_br_specialized prog r in
  (pt,r)   

and normalize_frac_branch_ctx prog (pt,bctx) = (pt, normalize_frac_ctx prog bctx)
  
(*and prune_list_ctx prog ctx = match ctx with
  | SuccCtx c -> SuccCtx (List.map (prune_ctx prog) c)
  | _ -> ctx*)

and prune_ctx_list prog ctx = List.map (fun (c1,c2)->(c1,List.map (prune_branch_ctx prog) c2)) ctx

and normalize_frac_ctx_list prog ctx= List.map (fun (c1,c2)->(c1,List.map (normalize_frac_branch_ctx prog) c2)) ctx

and prune_ctx_failesc_list prog ctx = List.map (fun (c1,c2,c3)-> 
    let rc3 = List.map (prune_branch_ctx prog) c3 in
    (c1,c2,rc3))  ctx

and normalize_frac_ctx_failesc_list prog ctx = List.map (fun (c1,c2,c3)-> 
    let rc3 = List.map (normalize_frac_branch_ctx prog) c3 in
    (c1,c2,rc3))  ctx
    
and prune_pred_struc prog (simp_b:bool) f = 
  let pr = Cprinter.string_of_struc_formula in
  Gen.Debug.no_1 "prune_pred_struc" pr pr (fun _ -> prune_pred_struc_x prog simp_b f) f 

and prune_pred_struc_x prog (simp_b:bool) f = 
  let rec helper f =
    if (is_no_heap_ext_formula f) then f
    else
      match f with
        | ECase c -> ECase {c with formula_case_branches = List.map (fun (c1,c2)-> 
              (* let mc1 = MCP.memoise_add_pure_P (MCP.mkMTrue no_pos) c1 in *)
              (* let c2 = combine_struc c2 ( mc1) in *)
              (c1,prune_pred_struc_x prog simp_b c2)) c.formula_case_branches;}
        | EBase b -> EBase {b with formula_ext_base = prune_preds prog simp_b b.formula_ext_base;
              formula_ext_continuation = prune_pred_struc_x prog simp_b b.formula_ext_continuation}
        | EAssume (v,f,l) -> EAssume (v,prune_preds prog simp_b f,l)
        | EVariance v -> EVariance v
  in    
  (*let _ = print_string ("prunning: "^(Cprinter.string_of_struc_formula f)^"\n") in*)
  List.map helper f


and normalize_frac_heap_deep prog (f:formula) = 
					let rec m_find (f:h_formula list->bool) (l:h_formula list list) = match l with 
						| [] -> ([],[])
						| h::t -> 
							if (f h) then (h,t) 
							else let r,l = m_find f t in (r,h::l) in
					let unfold_filter l = 
						if (List.exists is_view l)&&(List.exists is_data l) then List.filter is_view l
						else [] in
					let rec h_a_grp_f aset l :(h_formula list list) = match l with 
					   | [] -> []
					   | h::t -> 
						 let v = get_node_var h in
						 let a = v::(MCP.get_aset aset v) in
						 let t = h_a_grp_f aset t in
						 let lha, lhna = m_find (fun c-> Gen.BList.mem_eq CP.eq_spec_var (get_node_var (List.hd c)) a) t in
						 (h::lha):: lhna in	
					let rec perm_folder (h,l) = match l with
						| v1::v2::[]-> 
							let pv1 = Pr.mkVPerm v1 in
							let pv2 = Pr.mkVPerm v2 in
							(Pr.mkJoin pv1 pv2 (Pr.mkVPerm h) no_pos,[])
						| v1::t-> 
							let pv1 = Pr.mkVPerm v1 in
							let n_e = Pr.fresh_perm_var () in
							let rf,rev = perm_folder (n_e,t) in
							let nf = Pr.mkAnd rf (Pr.mkJoin pv1 (Pr.mkVPerm n_e) (Pr.mkVPerm h) no_pos) no_pos in
							(nf,n_e::rev)
						| _-> report_error no_pos ("perm_folder: must have at least two nodes to merge")	in
		let comb_hlp pos (ih,ip,ipr,iqv) l= match l with
		    | [] -> report_error no_pos ("normalize_frac_heap: must have at least one node in the aliased list")
			| h::[] -> (mkStarH_nn h ih pos,ip,ipr,iqv)
			| h::dups -> 
				if (List.exists (fun c->[]=(get_node_perm c))l) then (HFalse,ip,ipr,iqv)
				else 
					let n_p_v = Pr.fresh_perm_var () in
					let n_h = set_perm_node (Some n_p_v) h in
					let v = get_node_var h in
					let args = v::(get_node_args h) in
					let p,lpr = List.fold_left (fun (a1,a2) c ->
						let lv = (get_node_var c)::(get_node_args c) in
						let lp = List.fold_left2  (fun a v1 v2-> CP.mkAnd a (CP.mkEqVar v1 v2 pos) pos) a1 args lv in
					   (lp,(get_node_perm c)@a2)) (ip,get_node_perm h) dups in	
					let npr,n_e = perm_folder (n_p_v,lpr) in
					let n_h = mkStarH_nn n_h ih pos in
					let npr = Pr.mkAnd ipr npr pos in
					(n_h, p, npr , n_p_v::n_e@iqv) in 
		  let comb_hlp_l l f n_simpl_h :formula= 
        let (qv, h, p, t, fl, pr, br, lbl, pos) = all_components f in	 
        let nh,np,npr,qv = List.fold_left (comb_hlp pos) (n_simpl_h,CP.mkTrue pos,pr,qv) l in
        let np =  MCP.memoise_add_pure_N p np in
        mkExists_w_lbl qv nh np t fl npr br pos lbl in
				
		  let appl_comb_lemmas f w_lem h_alias_grp n_simpl_h :formula= 
        print_string "could have used a lemma for joining these predicates, for now join trivially";
        comb_hlp_l h_alias_grp f n_simpl_h  in
  let _ = 
  if  not !Globals.enable_frac_perm then f
  else 
	 let (qv, h, p, t, fl, pr, br, lbl, pos) = all_components f in	 
   let aset = MCP.comp_aliases p in
	 let l1 = split_h h in
	 let simpl_h, n_simpl_h = List.partition (fun c-> match c with | DataNode _ | ViewNode _ -> true | _ -> false) l1 in
	 let n_simpl_h = star_list n_simpl_h pos in
	 let h_alias_grp = h_a_grp_f aset simpl_h in	 
	 let n_unfold_l = List.concat (List.map unfold_filter h_alias_grp) in
	 if n_unfold_l <>[] then 
		let nf = List.fold_left (fun a c-> unfold_nth 8 (prog,None) a (get_node_var c) true 0 pos) f n_unfold_l in
		normalize_frac_formula prog nf 
	 else 
		let w_lem, wo_lem = List.partition (fun l -> 
			let hn,t = get_node_name (List.hd l), List.tl l in
			List.exists (fun c -> (String.compare hn (get_node_name c))<>0) t) h_alias_grp in
		if w_lem <>[] then 
			let nf = appl_comb_lemmas f w_lem h_alias_grp n_simpl_h in
			normalize_frac_formula prog nf 
		else 
		  let f = comb_hlp_l h_alias_grp f n_simpl_h in
		  if List.exists (fun c-> (List.length c) >1) h_alias_grp then  normalize_frac_formula prog f
		  else f in
    f
    
    
and normalize_frac_heap_shallow_a prog (f:formula) = 
	let rec m_find (f:h_formula list->bool) (l:h_formula list list) = match l with 
						| [] -> ([],[])
						| h::t -> 
							if (f h) then (h,t) 
							else let r,l = m_find f t in (r,h::l) in
					let rec h_a_grp_f aset l :(h_formula list list) = match l with 
					   | [] -> []
					   | h::t -> 
						 let v = get_node_var h in
						 let a = v::(MCP.get_aset aset v) in
						 let t = h_a_grp_f aset t in
						 let lha, lhna = m_find (fun c-> Gen.BList.mem_eq CP.eq_spec_var (get_node_var (List.hd c)) a) t in
						 (h::lha):: lhna in	
					let rec perm_folder (h,l) = match l with
						| v1::v2::[]-> 
							let pv1 = Pr.mkVPerm v1 in
							let pv2 = Pr.mkVPerm v2 in
							(Pr.mkJoin pv1 pv2 (Pr.mkVPerm h) no_pos,[])
						| v1::t-> 
							let pv1 = Pr.mkVPerm v1 in
							let n_e = Pr.fresh_perm_var () in
							let rf,rev = perm_folder (n_e,t) in
							let nf = Pr.mkAnd rf (Pr.mkJoin pv1 (Pr.mkVPerm n_e) (Pr.mkVPerm h) no_pos) no_pos in
							(nf,n_e::rev)
						| _-> report_error no_pos ("perm_folder: must have at least two nodes to merge")	in
		let comb_hlp pos (ih,ip,ipr,iqv) l= match l with
		    | [] -> report_error no_pos ("normalize_frac_heap: must have at least one node in the aliased list")
			| h::[] -> (mkStarH_nn h ih pos,ip,ipr,iqv)
			| h::dups -> 
				if (List.exists (fun c->[]=(get_node_perm c))l) then (HFalse,ip,ipr,iqv)
				else 
					let n_p_v = Pr.fresh_perm_var () in
					let n_h = set_perm_node (Some n_p_v) h in
					let v = get_node_var h in
					let args = v::(get_node_args h) in
					let p,lpr = List.fold_left (fun (a1,a2) c ->
						let lv = (get_node_var c)::(get_node_args c) in
						let lp = List.fold_left2  (fun a v1 v2-> CP.mkAnd a (CP.mkEqVar v1 v2 pos) pos) a1 args lv in
					   (lp,(get_node_perm c)@a2)) (ip,get_node_perm h) dups in	
					let npr,n_e = perm_folder (n_p_v,lpr) in
					let n_h = mkStarH_nn n_h ih pos in
					let npr = Pr.mkAnd ipr npr pos in
					(n_h, p, npr , n_p_v::n_e@iqv) in 
		  let comb_hlp_l l f n_simpl_h :formula= 
        let (qv, h, p, t, fl, pr, br, lbl, pos) = all_components f in	 
        let nh,np,npr,qv = List.fold_left (comb_hlp pos) (n_simpl_h,CP.mkTrue pos,pr,qv) l in
        let np =  MCP.memoise_add_pure_N p np in
        mkExists_w_lbl qv nh np t fl npr br pos lbl in
				
  let f = 
  if  not !Globals.enable_frac_perm then f
  else 
	 let (qv, h, p, t, fl, pr, br, lbl, pos) = all_components f in	 
   let aset = MCP.comp_aliases p in
	 let l1 = split_h h in
	 let simpl_h, n_simpl_h = List.partition (fun c-> match c with | DataNode _ -> true | _ -> false) l1 in
	 let n_simpl_h = star_list n_simpl_h pos in
	 let h_alias_grp = h_a_grp_f aset simpl_h in	 
	 let f = comb_hlp_l h_alias_grp f n_simpl_h in
	 if List.exists (fun c-> (List.length c) >1) h_alias_grp then  normalize_frac_formula prog f
	 else f in
    f

and normalize_frac_heap_shallow prog f = 
  let pr  =Cprinter.string_of_formula in
  Gen.Debug.no_1 "normalize_frac_heap_shallow" pr pr (normalize_frac_heap_shallow_a prog) f


and normalize_frac_heap prog (f:formula) = normalize_frac_heap_shallow prog f
  
and normalize_frac_heap_w prog h p =  (*used after adding back the consumed heap*)
   if  not !Globals.enable_frac_perm then (h,Cpr.mkTrue no_pos, MCP.mkMTrue no_pos,[])
   else 
      let f = normalize_frac_heap prog (mkBase h p TypeTrue (mkTrueFlow ()) (Pr.mkTrue no_pos) [] no_pos) in 
      match f with
        | Or _ -> Error.report_error {Err.error_loc = no_pos;Err.error_text = "normalize_frac_heap_w: adding the consumed heap should not yield OR"} 
        | _ ->
          let (qv, h, p, _, _, pr, _,_, _) = all_components f in	 
          (h,pr,p,qv)
  
and normalize_frac_formula prog f = match f with
 | Or b -> mkOr (normalize_frac_formula prog b.formula_or_f1) (normalize_frac_formula prog b.formula_or_f2) b.formula_or_pos
 | Base b -> normalize_frac_heap prog f
 | Exists e -> normalize_frac_heap prog f
  
and normalize_frac_struc prog f = 
	let hlp f = match f with
		| ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> (c1,normalize_frac_struc prog c2)) b.formula_case_branches;}
		| EBase b->  EBase{b with 
			formula_ext_base = normalize_frac_formula prog b.formula_ext_base; 
			formula_ext_continuation = normalize_frac_struc prog b.formula_ext_continuation }
		| EAssume (l,f,lbl) -> EAssume (l,normalize_frac_formula prog f , lbl)
		| EVariance b-> EVariance {b with formula_var_continuation = normalize_frac_struc prog b.formula_var_continuation} in
	List.map hlp f
    
and prune_preds_x prog (simp_b:bool) (f:formula):formula =   
  let imply_w f1 f2 = let r,_,_ = TP.imply f1 f2 "elim_rc" false None in r in   
  let f_p_simp c = if simp_b then MCP.elim_redundant(*_debug*) (imply_w,TP.simplify_a 3) c else c in
  let rec fct i op oh opr= if (i== !Globals.prune_cnt_limit) then (op,oh)
  else
    let nh, mem, changed = heap_prune_preds_mix prog oh op opr in 
    if changed then fct (i+1) mem nh opr
    else ((match op with | MCP.MemoF f -> MCP.MemoF (MCP.reset_changed f)| _ -> op) ,oh) in
  let rec helper_formulas f = match f with
    | Or o -> 
          let f1 = helper_formulas o.formula_or_f1 in
          let f2 = helper_formulas o.formula_or_f2 in
          mkOr f1 f2 o.formula_or_pos
              (*Or {o with formula_or_f1 = f1; formula_or_f2 = f2;}*)
    | Exists e ->    
      let pr_sol  = Cpr.solve_once e.formula_exists_perm in
      let rp,rh = fct 0 e.formula_exists_pure e.formula_exists_heap pr_sol in 
		  let rp = f_p_simp rp in  
		  let f = mkExists_w_lbl e.formula_exists_qvars rh rp e.formula_exists_type e.formula_exists_flow e.formula_exists_perm 
              e.formula_exists_branches e.formula_exists_pos e.formula_exists_label in
              (*Exists {e with formula_exists_pure = rp; formula_exists_heap = rh}*)
		  normalize_frac_formula prog f
          (*let rh, rp0,rpr0,nev0 = normalize_--frac_heap rh rp in let rp = f_p_simp (MCP.merge_mems rp rp0 false) in  
			let rpr = Cpr.mkAnd rpr0 e.formula_exists_perm no_pos in
          mkExists_w_lbl (e.formula_exists_qvars@nev0) rh rp e.formula_exists_type e.formula_exists_flow rpr e.formula_exists_branches e.formula_exists_pos e.formula_exists_label (*Exists {e with formula_exists_pure = rp; formula_exists_heap = rh}*)*)
    | Base b ->
      let pr_sol = Cpr.solve_once b.formula_base_perm in
      let rp,rh = fct 0 b.formula_base_pure b.formula_base_heap pr_sol in 
		  let rp = f_p_simp rp in
      let f = mkBase_w_lbl rh rp b.formula_base_type  b.formula_base_flow b.formula_base_perm b.formula_base_branches b.formula_base_pos b.formula_base_label in
		  normalize_frac_formula prog f
		  (*let rh, rp0,rpr0,nev0 = normalize_frac_heap rh rp in
          let rp = f_p_simp (MCP.merge_mems rp rp0 false) in
          let rpr = Cpr.mkAnd rpr0 b.formula_base_perm no_pos in
          if (List.length nev0 =0) then 
            mkBase_w_lbl rh rp b.formula_base_type  b.formula_base_flow rpr b.formula_base_branches b.formula_base_pos b.formula_base_label
          else mkExists_w_lbl nev0 rh rp b.formula_base_type b.formula_base_flow rpr
              b.formula_base_branches b.formula_base_pos b.formula_base_label *) in
  if not !Globals.allow_pred_spec then f
  else 
    (
        Gen.Profiling.push_time "prune_preds_filter";
        let f1 = filter_formula_memo f simp_b in
        Gen.Profiling.pop_time "prune_preds_filter";
        Gen.Profiling.push_time "prune_preds";
        let nf = helper_formulas f1 in   
        Gen.Profiling.pop_time "prune_preds";
        nf)

and prune_preds  prog (simp_b:bool) (f:formula):formula =   
  let p1 = string_of_bool in
  let p2 = Cprinter.string_of_formula in
  Gen.Debug.no_2 "prune_preds" p1 p2 p2 (fun _ _ -> prune_preds_x prog simp_b f) simp_b f

and heap_prune_preds_mix prog (hp:h_formula) (old_mem:MCP.mix_formula) pr: (h_formula*MCP.mix_formula*bool)= match old_mem with
  | MCP.MemoF f -> 
        let r1,r2,r3 = heap_prune_preds prog hp f [] pr in
        (r1, MCP.MemoF r2, r3)
  | MCP.OnePF _ -> (hp,old_mem,false)

and heap_prune_preds prog (hp:h_formula) (old_mem:MCP.memo_pure) ba_crt prf: (h_formula*MCP.memo_pure*bool)= 
  let pr = Cprinter.string_of_h_formula in
  let pr1 = Cprinter.string_of_memo_pure_formula in
  let pr2 (h,o,r) = pr_triple Cprinter.string_of_h_formula pr1 string_of_bool (h,o,r) in
  Gen.Debug.no_2 "heap_prune_preds" pr pr1 pr2 (fun _ _ -> heap_prune_preds_x prog hp old_mem ba_crt prf) hp old_mem

and heap_prune_preds_x prog (hp:h_formula) (old_mem:MCP.memo_pure) ba_crt pr: (h_formula*MCP.memo_pure*bool)= 
  match hp with
    | Star s ->
          let ba1 =ba_crt@(heap_baga prog s.h_formula_star_h1 pr) in
          let ba2 =ba_crt@(heap_baga prog s.h_formula_star_h2 pr) in
          let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_star_h1 old_mem ba2 pr in
          let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_star_h2 mem1 ba1 pr in
          let h = mkStarH_nn h1 h2 s.h_formula_star_pos in
          (h, mem2 , (changed1 or changed2))
              (*(Star {  
                h_formula_star_h1 = h1;
                h_formula_star_h2 = h2;
                h_formula_star_pos = s.h_formula_star_pos }, mem2, (changed1 or changed2) )*)
    | Conj s ->
          let ba1 =ba_crt@(heap_baga prog s.h_formula_conj_h1 pr) in
          let ba2 =ba_crt@(heap_baga prog s.h_formula_conj_h2 pr) in
          let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_conj_h1 old_mem ba2 pr in
          let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_conj_h2 mem1 ba1 pr in
          (Conj {  
              h_formula_conj_h1 = h1;
              h_formula_conj_h2 = h2;
              h_formula_conj_pos = s.h_formula_conj_pos }, mem2, (changed1 or changed2) )
    |Phase  s ->
         let ba1 =ba_crt@(heap_baga prog s.h_formula_phase_rd pr) in
         let ba2 =ba_crt@(heap_baga prog s.h_formula_phase_rw pr) in
         let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_phase_rd old_mem ba2 pr in
         let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_phase_rw mem1 ba1 pr in
         (Phase {  
             h_formula_phase_rd = h1;
             h_formula_phase_rw = h2;
             h_formula_phase_pos = s.h_formula_phase_pos }, mem2, (changed1 or changed2) )
    | Hole _
    | HTrue 
    | HFalse -> (hp, old_mem, false) 
    | DataNode d ->       
          (match d.h_formula_data_remaining_branches with
            | Some l -> (hp, old_mem, false)
            | None -> 
                  let not_null_form = CP.BForm (CP.Neq (CP.Var (d.h_formula_data_node,no_pos),CP.Null no_pos,no_pos), None) in
                  let null_form = CP.Eq (CP.Var (d.h_formula_data_node,no_pos),CP.Null no_pos,no_pos) in
                  let br_lbl = [(1,"")] in
                  let new_hp = DataNode{d with 
	                  h_formula_data_remaining_branches = Some br_lbl;
	                  h_formula_data_pruning_conditions = [ (null_form,br_lbl)];} in
                  let new_mem = MCP.memoise_add_pure_P_m old_mem  not_null_form in
                  (new_hp, new_mem, true))           
    | ViewNode v ->   
          let v_def = look_up_view_def v.h_formula_view_pos prog.prog_view_decls v.h_formula_view_name in
          let fr_vars = (CP.SpecVar (Named v_def.view_data_name, self, Unprimed)):: v_def.view_vars in
          let to_vars = v.h_formula_view_node :: v.h_formula_view_arguments in
          let zip = List.combine fr_vars to_vars in
          let zip_pr = List.combine fr_vars (Cpr.var_2_prop_var_list pr to_vars v.h_formula_view_perm) in
          let (rem_br, prun_cond,first_prune,chg) =  
            match v.h_formula_view_remaining_branches with
              | Some l -> 
                    let c = if (List.length l)<=1 then false else true in
                    if !no_incremental then
                      let new_cond = List.map (fun (c1,c2)-> (CP.b_subst zip c1,c2)) v_def.view_prune_conditions in         
                      (v_def.view_prune_branches,new_cond ,true,c)
                    else (l, v.h_formula_view_pruning_conditions,false,c)
              | None ->
                    let new_cond = List.map (fun (c1,c2)-> (CP.b_subst zip c1,c2)) v_def.view_prune_conditions in         
                    (v_def.view_prune_branches,new_cond ,true,true) in                   
          if (not chg) then 
            (ViewNode{v with h_formula_view_remaining_branches = Some rem_br; h_formula_view_pruning_conditions = [];}, old_mem,false)
          else
            (*decide which prunes can be activated and drop the ones that are implied while keeping the old unknowns*)
            let l_prune,l_no_prune, new_mem2 = List.fold_left 
              (fun (yes_prune, no_prune, new_mem) (p_cond, pr_branches)->            
                  if (Gen.BList.subset_eq (=) rem_br pr_branches) then (yes_prune, no_prune,new_mem)
                  else
                    if ((List.length (Gen.BList.intersect_eq (=) pr_branches rem_br))=0) then (yes_prune, no_prune,new_mem)
                    else try
                      let fv = CP.bfv p_cond in
                      let corr = MCP.memo_find_relevant_slice fv new_mem in
                      if not (MCP.memo_changed corr) then (yes_prune,(p_cond, pr_branches)::no_prune,new_mem)
                      else 
                        let p_cond_n = MCP.memo_f_neg_norm p_cond in
                        let y_p = if !no_memoisation then None else
                          (Gen.Profiling.inc_counter "syn_memo_count";
                          MCP.memo_check_syn_fast(*_prun*)(*_debug*) (p_cond,p_cond_n, pr_branches) rem_br corr) in
                        match y_p with
                          | Some y_p ->
                                (Gen.Profiling.inc_counter "syn_memo_hit";
                                (*let _ = print_string ("found contra: "^(String.concat " ; "(List.map (fun (c,_) -> string_of_int c) y_p))^"-\n") in*)
                                (y_p@yes_prune, no_prune,new_mem))
                          | None -> 
                                (*decide if i ^ a = false*)
                                (* let _ = print_string ("memo miss: "^(Cprinter.string_of_b_formula p_cond)^"\n") in
                                   let _ = print_string (" memo formula: "^(Cprinter.string_of_memoised_list [corr])^"\n") in                    
                                   let _ = print_string ("init mem: "^(Cprinter.string_of_memoised_list [corr])^"\n") in
                                   let _ = print_string ("and_is: "^(Cprinter.string_of_pure_formula and_is)^"\n") in
                                   let _ = print_string ("pcond: "^(Cprinter.string_of_b_formula p_cond)^"\n") in
                                *) 
                                let imp = 
                                  let and_is = MCP.fold_mem_lst_cons (CP.BConst (true,no_pos)) [corr] false true !Globals.prune_with_slice in
                                  let r = if (!Globals.enable_fast_imply) then 
                                    (*let r1,_,_ = TP.imply_msg_no_no and_is (CP.BForm (p_cond_n,None)) "prune_imply" "prune_imply" true None in
                                      let _ = if r1 then 
                                      print_string ("would have succeded:in proving: "^ (Cprinter.string_of_b_formula p_cond_n)^" (disproving "^
                                      (Cprinter.string_of_b_formula p_cond)^")\n for: "^
                                      (Cprinter.string_of_pure_formula and_is)^"\n")
                                      else () in*)
                                    false
                                  else 
                                    let r1,_,_ = TP.imply_msg_no_no and_is (CP.BForm (p_cond_n,None)) "prune_imply" "prune_imply" true None in
                                    (if r1 then Gen.Profiling.inc_counter "imply_sem_prun_true"
                                    else Gen.Profiling.inc_counter "imply_sem_prun_false";r1) in
                                  r
					                  (*| _ -> 
                                        Gen.Profiling.inc_counter "fast_imply_likely_false";
                                        false (*definitely false*) (*| -1 (*likely false*) | 0 (*don't know*)*)*)in
                                      (*let and_is = MCP.fold_mem_lst_cons p_cond [corr] false true false  in
                                        let sat = TP.is_sat_msg_no_no "prune_sat" and_is true in*)
                                if imp then (*there was a contradiction*)
                                  let nyp = pr_branches@yes_prune in
                                  let mem_w_fail = MCP.memoise_add_failed_memo new_mem p_cond_n in
                                  (nyp,no_prune,mem_w_fail)
                                else (yes_prune,(p_cond, pr_branches)::no_prune,new_mem)
                    with | Not_found -> (yes_prune, (p_cond, pr_branches)::no_prune, new_mem)
              ) ([],[], old_mem) prun_cond in
            
            let l_prune' = 
              let aliases = MCP.memo_get_asets (List.map fst ba_crt) new_mem2 in
              let ba_crt = ba_crt@(List.concat(List.map (fun (c,n)->List.map (fun c-> c,n)(CP.EMapSV.find_equiv_all c aliases)) ba_crt)) in
              let n_l = List.filter (fun c-> 
                  let c_ba,_ = List.find (fun (_,d)-> c=d) v_def.view_prune_conditions_baga in
                  let c_ba = Gen.BList.list_substs (fun b a-> P.eq_spec_var (fst a) (fst b)) zip_pr c_ba in
                  not (Gen.BList.disjoint_eq CP.PtrSV.eq (*CP.eq_spec_var*) ba_crt c_ba)) rem_br in
              Gen.BList.remove_dups_eq (=) (l_prune@n_l) in
            let l_prune = if (List.length l_prune')=(List.length rem_br) then l_prune else l_prune' in
            
            (*l_prune : branches that will be dropped*)
            (*l_no_prune: constraints that overlap with the implied set or are part of the unknown, remaining prune conditions *)
            (*rem_br : formula_label list  -> remaining branches *)         
            (*let _ = print_string ("pruned cond active: "^(string_of_int (List.length l_prune))^"\n") in*)
            let (r_hp, r_memo, r_b) = if ((List.length l_prune)>0) then  
              let posib_dismised = Gen.BList.remove_dups_eq (=) l_prune in
              let rem_br_lst = List.filter (fun c -> not (List.mem c posib_dismised)) rem_br in
              if (rem_br_lst == []) then (HFalse, MCP.mkMFalse_no_mix no_pos, true)
              else 
                let l_no_prune = List.filter (fun (_,c)-> (List.length(Gen.BList.intersect_eq (=) c rem_br_lst))>0) l_no_prune in
                (*let _ = print_endline " heap_prune_preds: ViewNode->Update branches" in *)
                let new_hp = ViewNode {v with 
                    h_formula_view_remaining_branches = Some rem_br_lst;
                    h_formula_view_pruning_conditions = l_no_prune;} in
                let dism_invs = if first_prune then [] else (lookup_view_invs_with_subs rem_br v_def zip) in
                let added_invs = (lookup_view_invs_with_subs rem_br_lst v_def zip) in
                let new_add_invs = Gen.BList.difference_eq CP.eq_b_formula_no_aset added_invs dism_invs in
                let old_dism_invs = Gen.BList.difference_eq CP.eq_b_formula_no_aset dism_invs added_invs in
                let ni = MCP.create_memo_group_wrapper new_add_invs MCP.Implied_P in
                (*let _ = print_string ("adding: "^(Cprinter.string_of_memoised_list ni)^"\n") in*)
                let mem_o_inv = MCP.memo_change_status old_dism_invs new_mem2 in 
                ( Gen.Profiling.inc_counter "prune_cnt"; Gen.Profiling.add_to_counter "dropped_branches" (List.length l_prune);
                (new_hp, MCP.merge_mems_m mem_o_inv ni true, true) )
            else 
              if not first_prune then 
                (ViewNode{v with h_formula_view_pruning_conditions = l_no_prune;},new_mem2, false)
              else 
                let ai = (lookup_view_invs_with_subs rem_br v_def zip) in
                let gr_ai = MCP.create_memo_group_wrapper ai MCP.Implied_P in     
                let l_no_prune = List.filter (fun (_,c)-> (List.length(Gen.BList.intersect_eq (=) c rem_br))>0) l_no_prune in
                let new_hp = ViewNode {v with  h_formula_view_remaining_branches = Some rem_br;h_formula_view_pruning_conditions = l_no_prune;} in
                (new_hp, MCP.merge_mems_m new_mem2 gr_ai true, true) in
            (r_hp,r_memo,r_b)

and split_linear_node (h : h_formula) : (h_formula * h_formula) list = split_linear_node_guided [] h

(* and split_linear_node (h : h_formula) : (h_formula * h_formula) =  *)
(*         let prh = Cprinter.string_of_h_formula in *)
(*         let pr (h1,h2) = "("^(prh h1)^","^(prh h2)^")" in *)
(*         Gen.Debug.no_1 "split_linear_node" Cprinter.string_of_h_formula pr split_linear_node_x h *)

(* (\* split conseq to a node to be checked at the next step and *\) *)
(* (\* a the remaining part to be checked recursively            *\) *)
(* and split_linear_node_x (h : h_formula) : (h_formula * h_formula) =  *)
(*         let rec helper h = *)
(*           match h with *)
(*             | HTrue -> (HTrue, HTrue) *)
(*             | HFalse -> (HFalse, HFalse) *)
(*             | Hole _ -> report_error no_pos  "Immutability annotation encountered\n"    *)
(*             | DataNode _ | ViewNode _ -> (h, HTrue) *)
(*             | Star ({h_formula_star_h1 = h1; *)
(* 	          h_formula_star_h2 = h2; *)
(* 	          h_formula_star_pos = pos}) -> *)
(*                   begin *)
(* 	                match h1 with *)
(* 	                  | HTrue -> print_string ("\n\n!!!This shouldn't happen!!!\n\n"); helper h2 (\* this shouldn't happen anyway *\) *)
(* 	                  | _ -> *)
(* 	                        let ln1, r1 = helper h1 in *)
(* 	                        (ln1, mkStarHh r1 h2 pos) *)
(*                   end *)
(*             | Phase ({h_formula_phase_rd = h1; *)
(* 	          h_formula_phase_rw = h2; *)
(* 	          h_formula_phase_pos = pos}) -> *)
(*                   begin *)
(* 	                match h1 with *)
(* 	                  | HTrue -> print_string ("\n\n!!!This shouldn't happen!!!\n\n"); helper h2 (\* this shouldn't happen anyway *\) *)
(* 	                  | _ -> *)
(* 	                        let ln1, r1 = helper h1 in *)
(* 	                        (ln1, mkPhaseH r1 h2 pos) *)
(*                   end *)
(*             | Conj ({h_formula_conj_h1 = h1; *)
(* 	          h_formula_conj_h2 = h2; *)
(* 	          h_formula_conj_pos = pos}) ->  *)
(*                   begin *)
(* 	                match h1 with *)
(* 	                  | HTrue -> print_string ("\n\n!!!This shouldn't happen!!!\n\n"); helper h2 (\* this shouldn't happen anyway *\) *)
(* 	                  | _ -> *)
(* 	                        let ln1, r1 = helper h1 in *)
(* 	                        (ln1, mkConjH r1 h2 pos) *)
(*                   end in *)
(*         helper h *)

and split_linear_node_guided (vars : CP.spec_var list) (h : h_formula) : (h_formula * h_formula) list = 
  let prh = Cprinter.string_of_h_formula in
  let pr l= String.concat "," (List.map (fun (h1,h2)->"("^(prh h1)^","^(prh h2)^")") l) in
  Gen.Debug.no_2 "split_linear_node_guided" Cprinter.string_of_spec_var_list Cprinter.string_of_h_formula pr split_linear_node_guided_x vars h

(* split h into (h1,h2) with one node from h1 and the rest in h2 *)

and split_linear_node_guided_x (vars : CP.spec_var list) (h : h_formula) : (h_formula * h_formula) list = 
  let rec splitter h1 h2 constr pos = 
    let l1 = sln_helper h1 in
    let l2 = sln_helper h2 in
    let l1r = List.map (fun (c1,c2)->(c1,constr c2 h2 pos)) l1 in
    let l2r = List.map (fun (c1,c2)->(c1,constr h1 c2 pos)) l2 in
    l1r@l2r 
  and sln_helper h = match h with
    | HTrue  
    | HFalse -> [(h,h)]
    | Hole _ -> report_error no_pos "[solver.ml]: Immutability hole annotation encountered\n"	
    | DataNode _ 
    | ViewNode _ -> [(h,HTrue)]
    | Conj  h-> splitter h.h_formula_conj_h1 h.h_formula_conj_h2 mkConjH h.h_formula_conj_pos
    | Phase h-> splitter h.h_formula_phase_rd h.h_formula_phase_rw mkPhaseH h.h_formula_phase_pos
    | Star  h-> splitter h.h_formula_star_h1 h.h_formula_star_h2 mkStarH_nn h.h_formula_star_pos in
  let l = sln_helper h in
  List.filter (fun (c1,_)-> Cformula.is_complex_heap c1) l 

      
(*
  and split_linear_node_guided_x (vars : CP.spec_var list) (h : h_formula) : (h_formula * h_formula) = 
(*  let _ = print_string("in split_linear_node_guided with h = " ^ (Cprinter.string_of_h_formula h) ^ "\n") in*)
  let rec helper h =
  let splitter h1 h2 constr pos = match h1 with
  | HTrue -> print_string ("\n\n!!!This shouldn't happen!!!\n\n"); helper h2 (* this shouldn't happen anyway *)
  | _ ->
  let ln1, r1 = helper h1 in
  match ln1 with
  | HTrue -> let ln2, r2 = helper h2 in
  (ln2, constr h1 r2 pos)
  | ViewNode _ -> 
  let ln2, r2 = helper h2 in
  (match ln2 with
  | DataNode _ -> (ln2, constr h1 r2 pos)
  | _ ->(ln1, constr r1 h2 pos))
  | _     ->  (ln1, constr r1 h2 pos) in
  match h with
  | HTrue -> (HTrue, HTrue)
  | HFalse -> (HFalse, HFalse)
  | Hole _ -> report_error no_pos "[solver.ml]: Immutability hole annotation encountered\n"	
  | DataNode {h_formula_data_node = root; h_formula_data_imm = imm} 
  | ViewNode {h_formula_view_node = root; h_formula_view_imm = imm} ->
(* overwrite the default -> should not be needed once all the rules are implementes *)
  if (vars==[]) || (List.exists (CP.eq_spec_var root) vars) then (h, HTrue)
  else (HTrue,h)
  | Conj  h-> splitter h.h_formula_conj_h1 h.h_formula_conj_h2 mkConjH h.h_formula_conj_pos
  | Phase h-> splitter h.h_formula_phase_rd h.h_formula_phase_rw mkPhaseH h.h_formula_phase_pos
  | Star  h-> splitter h.h_formula_star_h1 h.h_formula_star_h2 mkStarHh h.h_formula_star_pos in
  helper h

  
  and h_mvars prog (h : h_formula) : CP.spec_var list = match h with
  | Star ({h_formula_star_h1 = h1;
  h_formula_star_h2 = h2;
  h_formula_star_pos = pos})
  | Phase ({h_formula_phase_rd = h1;
  h_formula_phase_rw = h2;
  h_formula_phase_pos = pos})
  | Conj ({h_formula_conj_h1 = h1;
  h_formula_conj_h2 = h2;
  h_formula_conj_pos = pos}) -> CP.remove_dups_svl (h_fv h1 @ h_fv h2)
  | DataNode ({h_formula_data_node = v}) -> [v]
  | ViewNode ({h_formula_view_node = v;
  h_formula_view_arguments = vargs;
  h_formula_view_name = c}) -> begin
  let vdef = look_up_view_def_raw prog.prog_view_decls c in
  let mvs = CP.subst_var_list_avoid_capture vdef.view_vars vargs vdef.view_materialized_vars in
  let mvars = if CP.mem v mvs then mvs else v :: mvs in
  mvars
  end
  | HTrue | HFalse | Hole _ -> []
*)
and get_equations_sets (f : CP.formula) (interest_vars:Cpure.spec_var list): (CP.b_formula list) = match f with
  | CP.And (f1, f2, pos) -> 
        let l1 = get_equations_sets f1 interest_vars in
        let l2 = get_equations_sets f2 interest_vars in
        l1@l2
  | CP.BForm (bf,_) -> begin
      match bf with
        | Cpure.BVar (v,l)-> [bf]
        | Cpure.Lt (e1,e2,l)-> 
	          if (Cpure.of_interest e1 e2 interest_vars) then [Cpure.Lt(e1,e2,l)]
	          else []
        | Cpure.Lte (e1,e2,l) -> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [Cpure.Lte(e1,e2,l)]
	          else []
        | Cpure.Gt (e1,e2,l) -> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [Cpure.Lt(e2,e1,l)]
	          else []
        | Cpure.Gte(e1,e2,l)-> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [Cpure.Lte(e2,e1,l)]
	          else []
        | Cpure.Eq (e1,e2,l) -> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [Cpure.Eq(e1,e2,l)]
	          else []
        | Cpure.Neq (e1,e2,l)-> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [Cpure.Neq(e1,e2,l)]
	          else []
        | _ -> []
    end	
  | CP.Not (f1,_,_) -> List.map (fun c-> match c with
      | Cpure.BVar (v,l)-> c
      | Cpure.Lt (e1,e2,l)-> Cpure.Lt (e2,e1,l)
      | Cpure.Lte (e1,e2,l) -> Cpure.Lte (e2,e1,l)
      | Cpure.Eq (e1,e2,l) -> Cpure.Neq (e1,e2,l) 
      | Cpure.Neq (e1,e2,l)-> Cpure.Eq (e1,e2,l)
      |_ ->Error.report_error { 
	         Error.error_loc = no_pos; 
	         Error.error_text ="malfunction:get_equations_sets must return only bvars, inequalities and equalities"}
    ) (get_equations_sets f1 interest_vars)
  | _ ->Error.report_error { 
        Error.error_loc = no_pos; 
        Error.error_text ="malfunction:get_equations_sets can be called only with conjuncts and without quantifiers"}

and combine_es_and prog (f : MCP.mix_formula) (reset_flag:bool) (es : entail_state) : context = 
  let r1,r2 = combine_and es.es_formula f in  
  if (reset_flag) then if r2 then (Ctx {es with es_formula = r1;es_unsat_flag =false;})
  else Ctx {es with es_formula = r1;}
  else Ctx {es with es_formula = r1;}

and combine_list_context_and_unsat_now prog (ctx : list_context) (f : MCP.mix_formula) : list_context = 
  let r = transform_list_context ((combine_es_and prog f true),(fun c->c)) ctx in
  let r = transform_list_context ((elim_unsat_es_now prog (ref 1)),(fun c->c)) r in
  TP.incr_sat_no () ; r

and list_context_and_unsat_now prog (ctx : list_context) : list_context = 
  let r = transform_list_context ((elim_unsat_es prog (ref 1)),(fun c->c)) ctx in
  TP.incr_sat_no () ; r

and list_partial_context_and_unsat_now prog (ctx : list_partial_context) : list_partial_context = 
  (* let r = transform_list_partial_context ((combine_es_and prog f true),(fun c->c)) ctx in *)
  let r = transform_list_partial_context ((elim_unsat_es_now prog (ref 1)),(fun c->c)) ctx in
  let r = remove_dupl_false_pc_list r in
  TP.incr_sat_no () ; r

and list_failesc_context_and_unsat_now prog (ctx : list_failesc_context) : list_failesc_context = 
  let r = transform_list_failesc_context (idf,idf,(elim_unsat_es prog (ref 1))) ctx in
  let r = List.map CF.remove_dupl_false_fe r in
  TP.incr_sat_no () ; r

and combine_list_failesc_context_and_unsat_now prog (ctx : list_failesc_context) (f : MCP.mix_formula) : list_failesc_context = 
  let r = transform_list_failesc_context (idf,idf,(combine_es_and prog f true)) ctx in
  let r = transform_list_failesc_context (idf,idf,(elim_unsat_es_now prog (ref 1))) r in
  let r = List.map CF.remove_dupl_false_fe r in
  TP.incr_sat_no () ; r


and combine_context_and_unsat_now prog (ctx : context) (f : MCP.mix_formula) : context = 
  let r = transform_context (combine_es_and prog f true) ctx in
  let r = transform_context (elim_unsat_es_now prog (ref 1)) r in
  TP.incr_sat_no () ; r
      (* expand all predicates in a definition *)

and context_and_unsat_now prog (ctx : context)  : context = 
  let r = transform_context (elim_unsat_es prog (ref 1)) ctx in
  TP.incr_sat_no () ; r
      (* expand all predicates in a definition *)

and expand_all_preds prog f0 do_unsat: formula = 
  match f0 with
    | Or (({formula_or_f1 = f1;
	  formula_or_f2 = f2}) as or_f) -> begin
        let ef1 = expand_all_preds prog f1 do_unsat in
        let ef2 = expand_all_preds prog f2 do_unsat in
        Or ({or_f with formula_or_f1 = ef1; formula_or_f2 = ef2})
      end
    | Base ({formula_base_heap = h;
	  formula_base_pure = p;
	  formula_base_pos =pos}) -> begin
        let proots = find_pred_roots_heap h in 
        let ef0 = List.fold_left (fun f -> fun v -> unfold_nth 3 (prog,None) f v do_unsat 0 pos ) f0 proots in
        ef0
      end
    | Exists ({ formula_exists_qvars = qvars;
	  formula_exists_heap = qh;
	  formula_exists_pure = qp;
	  formula_exists_perm = pr;
	  formula_exists_flow = fl;
      (* formula_exists_imm = imm; *)
	  formula_exists_label = lbl;
	  formula_exists_pos = pos}) -> begin
        let proots = find_pred_roots_heap qh in
        let f = Base ({formula_base_heap = qh;
		formula_base_pure = qp;
		formula_base_type = TypeTrue;
		formula_base_perm = pr;
	    (* formula_base_imm = imm; *)
		formula_base_flow = fl;
		formula_base_branches = [];
		formula_base_label = lbl;
		formula_base_pos = pos}) in
        let ef = List.fold_left (fun f -> fun v -> unfold_nth 4 (prog,None) f v do_unsat 0 pos  ) f proots in
        let ef0 = push_exists qvars ef in
        ef0
      end

and find_pred_roots f0 = match f0 with
  | Or ({formula_or_f1 = f1;
	formula_or_f2 = f2}) -> begin
      let pr1 = find_pred_roots f1 in
      let pr2 = find_pred_roots f2 in
      let tmp = CP.remove_dups_svl (pr1 @ pr2)  in
      tmp
    end
  | Base ({formula_base_heap = h;
	formula_base_pure = p;
	formula_base_pos =pos}) -> find_pred_roots_heap h
  | Exists ({formula_exists_qvars = qvars;
	formula_exists_heap = qh;
	formula_exists_pure = qp;
	formula_exists_pos = pos}) -> begin
      let tmp1 = find_pred_roots_heap qh in
      let tmp2 = Gen.BList.difference_eq CP.eq_spec_var tmp1 qvars in
      tmp2
    end

and find_pred_roots_heap h0 = 
  match h0 with
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos})
    | Conj ({h_formula_conj_h1 = h1;
	  h_formula_conj_h2 = h2;
	  h_formula_conj_pos = pos})
    | Phase ({h_formula_phase_rd = h1;
	  h_formula_phase_rw = h2;
	  h_formula_phase_pos = pos}) -> begin
        let pr1 = find_pred_roots_heap h1 in
        let pr2 = find_pred_roots_heap h2 in
        let tmp = CP.remove_dups_svl (pr1 @ pr2) in
        tmp
      end
    | ViewNode ({h_formula_view_node = p}) -> [p]
    | DataNode _ | HTrue | HFalse | Hole _ -> []

(* unfold then unsat *)
and unfold_context_unsat_now prog0 (prog:prog_or_branches) (ctx : list_context) (v : CP.spec_var) (pos : loc) : list_context =
  let ctx = unfold_context prog ctx v false pos in
  list_context_and_unsat_now prog0 ctx

(* unfolding *)
and unfold_context (prog:prog_or_branches) (ctx : list_context) (v : CP.spec_var) (already_unsat:bool)(pos : loc) : list_context =
  let fct es = 
    let unfolded_f = unfold_nth 5 prog es.es_formula v already_unsat 0 pos in
    let res = build_context (Ctx es) unfolded_f pos in
    if already_unsat then set_unsat_flag res true
    else res in 
  transform_list_context (fct,(fun c->c)) ctx 

and unfold_partial_context (prog:prog_or_branches) (ctx : list_partial_context) (v : CP.spec_var) (already_unsat:bool)(pos : loc) : list_partial_context =
  let fct es = 
    let unfolded_f = unfold_nth 6 prog es.es_formula v already_unsat 0 pos in
    let res = build_context (Ctx es) unfolded_f pos in
    if already_unsat then set_unsat_flag res true
    else res in 
  transform_list_partial_context (fct,(fun c->c)) ctx 

and unfold_failesc_context (prog:prog_or_branches) (ctx : list_failesc_context) (v : CP.spec_var) (already_unsat:bool)(pos : loc) : list_failesc_context =
  let fct es = 
    (* this came from unfolding for bind mostly *)
    let unfolded_f = unfold_nth 7 prog es.es_formula v already_unsat 0 pos in
    let res = build_context (Ctx es) unfolded_f pos in
    if already_unsat then set_unsat_flag res true
    else res in 
  transform_list_failesc_context (idf,idf,fct) ctx

and unfold_nth(*_debug*) (n:int) (prog:prog_or_branches) (f : formula) (v : CP.spec_var) (already_unsat:bool) (uf:int) (pos : loc) : formula =
  (* unfold_x prog f v already_unsat pos *)
  let pr = Cprinter.string_of_formula in
  Gen.Debug.no_2_num n "unfold" string_of_bool pr pr (fun _ _ -> unfold_x prog f v already_unsat uf pos) already_unsat f

and unfold_x (prog:prog_or_branches) (f : formula) (v : CP.spec_var) (already_unsat:bool) (uf:int) (pos : loc) : formula = match f with
  | Base ({ formula_base_heap = h;
	formula_base_pure = p;
	formula_base_branches = b;
	formula_base_perm = pr;
	formula_base_flow = fl;
	formula_base_pos = pos}) -> 
        (*let _ = print_string ("\n memo before unfold: "^(Cprinter.string_of_memoised_list mem)^"\n")in*)
        unfold_baref prog h p fl pr v pos b [] already_unsat uf
  | Exists _ -> (*report_error pos ("malfunction: trying to unfold in an existentially quantified formula!!!")*)
        let rf = rename_bound_vars f in
        let qvars, baref = split_quantifiers rf in
        let h, p, fl, pr, b, t = split_components baref in
        (*let _ = print_string ("\n memo before unfold: "^(Cprinter.string_of_memoised_list mem)^"\n")in*)
        let uf = unfold_baref prog h p fl pr v pos b qvars already_unsat uf in
        uf
  | Or ({formula_or_f1 = f1;
	formula_or_f2 = f2;
	formula_or_pos = pos}) ->
        let uf1 = unfold_x prog f1 v already_unsat uf pos in
        let uf2 = unfold_x prog f2 v already_unsat uf pos in
        let resform = mkOr uf1 uf2 pos in
        resform

and unfold_baref prog (h : h_formula) (p : MCP.mix_formula) (fl:flow_formula) pr (v : CP.spec_var) pos b qvars already_unsat (uf:int) : formula =
  let asets = MCP.alias_nth 6 (MCP.ptr_equations_with_null p) in
  let aset' = MCP.get_aset asets v in
  let aset = if CP.mem v aset' then aset' else v :: aset' in
  let unfolded_h = unfold_heap prog h aset v fl uf pos in
  let pure_f = mkBase HTrue p TypeTrue (mkTrueFlow ()) pr b pos in
  let tmp_form_norm = normalize_combine unfolded_h pure_f pos in
  let tmp_form = Cformula.set_flow_in_formula_override fl tmp_form_norm in
  let resform = if (List.length qvars) >0 then push_exists qvars tmp_form else tmp_form in
  (*let res_form = elim_unsat prog resform in*)
  if already_unsat then match (snd prog) with 
    | None -> 
          (Gen.Profiling.push_time "unfold_unsat";
          let r = elim_unsat_for_unfold (fst prog) resform in
          Gen.Profiling.pop_time "unfold_unsat";r)    
    | _ -> resform
  else resform

and unfold_heap prog (f : h_formula) (aset : CP.spec_var list) (v : CP.spec_var) fl (uf:int) pos : formula = 
  (*  let _ = print_string("unfold heap " ^ (Cprinter.string_of_h_formula f) ^ "\n\n") in*)
  match f with
    | ViewNode ({h_formula_view_node = p;
	  h_formula_view_imm = imm;       
	  h_formula_view_name = c;
	  h_formula_view_origins = origs;
	  h_formula_view_original = original;
	  h_formula_view_unfold_num = old_uf;
	  h_formula_view_label = v_lbl;
	  h_formula_view_remaining_branches = brs;
	  h_formula_view_perm = pr;
	  h_formula_view_arguments = vs}) ->(*!!Attention: there might be several nodes pointed to by the same pointer as long as they are empty*)
          let uf = old_uf+uf in
          if CP.mem p aset then
	        match (snd prog) with
	          | None ->
                    let prog = fst prog in
	                let vdef = Cast.look_up_view_def pos prog.prog_view_decls c in
                    (*let _ = print_string "\n y\n" in*)
                    let joiner f = formula_of_disjuncts (fst (List.split f)) in
                    let forms = match brs with 
                      | None -> formula_of_unstruc_view_f vdef
                      | Some s -> joiner (List.filter (fun (_,l)-> List.mem l s) vdef.view_un_struc_formula) in
	                let renamed_view_formula = rename_bound_vars forms in
	                let renamed_view_formula = add_unfold_num renamed_view_formula uf in
		            (* propagate the immutability annotation inside the definition *)
	                let renamed_view_formula = Cformula.propagate_imm_formula renamed_view_formula imm in
					let renamed_view_formula = Cformula.set_perm_formula renamed_view_formula (Pr.mkTrue pos) pr in
	                let fr_vars = (CP.SpecVar (Named vdef.view_data_name, self, Unprimed))
	                  :: vdef.view_vars in
	                let to_vars = v :: vs in
	                let res_form = subst_avoid_capture fr_vars to_vars renamed_view_formula in
			        (*let _ = print_string ("unfold pre subst: "^(Cprinter.string_of_formula renamed_view_formula)^"\n") in
			          let _ = print_string ("unfold post subst: "^(Cprinter.string_of_formula res_form)^"\n") in *)
	                let res_form = add_origins res_form origs in
				    let res_form = add_original res_form original in
		            (*let res_form = struc_to_formula res_form in*)
	                CF.replace_formula_label v_lbl res_form
	          | Some (base , br, to_vars) -> 
			        (* let _ = print_string "\n x\n" in*)
	                if (List.fold_left2 (fun a c1 c2-> a&&(c1=c2)) true to_vars vs) 
	                then  CF.replace_formula_label v_lbl  (CF.formula_of_mix_formula_with_branches_fl base br fl no_pos)
	                else formula_of_heap f pos
          else
	        formula_of_heap_fl f fl pos
    | Star ({h_formula_star_h1 = f1;
	  h_formula_star_h2 = f2}) ->
          let uf1 = unfold_heap prog f1 aset v fl uf pos in
          let uf2 = unfold_heap prog f2 aset v fl uf pos in
          normalize_combine_star uf1 uf2 pos
    | Conj ({h_formula_conj_h1 = f1;
	  h_formula_conj_h2 = f2}) ->
          let uf1 = unfold_heap prog f1 aset v fl uf pos in
          let uf2 = unfold_heap prog f2 aset v fl uf pos in
          normalize_combine_conj uf1 uf2 pos
    | Phase ({h_formula_phase_rd = f1;
	  h_formula_phase_rw = f2}) ->
          let uf1 = unfold_heap prog f1 aset v fl uf pos in
          let uf2 = unfold_heap prog f2 aset v fl uf pos in
          normalize_combine_phase uf1 uf2 pos
    | _ -> formula_of_heap_fl f fl pos

(*
  vvars: variables of interest
  evars: those involving this will be on the rhs
  otherwise move to the lhs
*)
and split_universal ((f0 : CP.formula), f0b) (evars : CP.spec_var list) 
      (expl_inst_vars : CP.spec_var list)(impl_inst_vars : CP.spec_var list)
      (vvars : CP.spec_var list) (pos : loc) 
      = let ((a,b),x,y)=split_universal_a (f0,f0b) evars expl_inst_vars impl_inst_vars vvars pos in
      ((elim_exists_pure_formula a,b),x,y)

and split_universal_debug ((f0 : CP.formula), f0b) (evars : CP.spec_var list) 
      (expl_inst_vars : CP.spec_var list)(impl_inst_vars : CP.spec_var list)
      (vvars : CP.spec_var list) (pos : loc) 
      =
  let vv = evars (*impl_inst_vars*) in
  Gen.Debug.no_2 "split_universal" (fun (f,_)->Cprinter.string_of_pure_formula f)
      (fun _ -> (Cprinter.string_of_spec_var_list evars)^"/I="^(Cprinter.string_of_spec_var_list impl_inst_vars)^"/E="^(Cprinter.string_of_spec_var_list expl_inst_vars)^"/"^ (Cprinter.string_of_spec_var_list vvars)) (fun ((f1,_),(f2,_),_) -> (Cprinter.string_of_pure_formula f1)^"/"^ (Cprinter.string_of_pure_formula f2)) (fun f vv -> split_universal f evars expl_inst_vars impl_inst_vars vvars pos)
      (f0,f0b) vv
      (*
        vvars: variables of interest
        evars: those involving this will be on the rhs
        otherwise move to the lhs
      *)
and split_universal_a ((f0 : CP.formula), f0b) (evars : CP.spec_var list) 
      (expl_inst_vars : CP.spec_var list)(impl_inst_vars : CP.spec_var list)
      (vvars : CP.spec_var list) (pos : loc) 
      : ((CP.formula * (branch_label * CP.formula) list) * 
          (CP.formula * (branch_label * CP.formula) list) * (CP.spec_var list)) =
  let rec split f = match f with
    | CP.And (f1, f2, _) ->
          let app1, cpp1 = split f1 in
          let app2, cpp2 = split f2 in
          (CP.mkAnd app1 app2 pos, CP.mkAnd cpp1 cpp2 pos)
    | _ ->
          let fvars = CP.fv f in
          if CP.disjoint fvars vvars then
	        (CP.mkTrue pos, CP.mkTrue pos) (* just ignore the formula in this case as
					                          it is disjoint
					                          from the set of variables of interest *)
          else
	        (*
	          - 23.05.2008 -
	          Current actions are:
	          (i) discard E2(g) which has already been proven
	          (ii) move E1(f.g) to LHS for implicit instantiation
	          (iii) leave E3(e,f,g) to RHS for linking existential var e

	          What we added here: -->Step (iii) can be also improved by additionally moving (exists e : E3(e,f,g)) to the LHS.
	        *)
	        if not (CP.disjoint (evars@expl_inst_vars@impl_inst_vars) fvars) then (* to conseq *)
	          (CP.mkTrue pos, f)
	        else (* to ante *)
	          (f, CP.mkTrue pos)
  in
  (* -- added on 21.05.2008 *)
  (* try to obtain as much as a CNF form as possible so that the splitting of bindings between antecedent and consequent is more accurate *)
  let f = (normalize_to_CNF f0 pos) in
  let fb = (List.map (fun (l,f) -> (l, normalize_to_CNF f pos)) f0b) in
  let to_ante, to_conseq = split f in
  let to_ante = CP.find_rel_constraints to_ante vvars in
  let tmp_l = List.map (fun (l, f) -> (l, split f)) fb in
  let labels, pairs = List.split tmp_l in
  let to_ante_f, to_conseq_f = List.split pairs in
  let to_ante_b, to_conseq_b = (List.combine labels to_ante_f), (List.combine labels to_conseq_f) in

  let conseq_fv = CP.fv to_conseq in
  let conseq_fv_b = (List.map (fun (l,f) -> CP.fv f) to_conseq_b) in
  let instantiate = List.filter (fun v -> List.mem v (evars@expl_inst_vars@impl_inst_vars)) conseq_fv in
  let instantiate_b = List.map (fun fv_list -> List.filter (fun v -> List.mem v (evars@expl_inst_vars@impl_inst_vars)) fv_list) conseq_fv_b in
  let wrapped_to_conseq = List.fold_left (fun f v -> CP.Exists (v, f,None, pos)) to_conseq instantiate in
  let wrapped_to_conseq_b = 
    List.map2 (fun to_conseq instantiate -> List.fold_left (fun f v -> CP.Exists (v, f, None, pos)) to_conseq instantiate)
        to_conseq_f instantiate_b in
  let to_ante =
    if CP.fv wrapped_to_conseq <> [] then CP.mkAnd to_ante wrapped_to_conseq no_pos else to_ante
  in
  let to_ante_f = List.map2 (fun to_ante wrapped_to_conseq ->
      if CP.fv wrapped_to_conseq <> [] then CP.mkAnd to_ante wrapped_to_conseq no_pos else to_ante
  ) to_ante_f wrapped_to_conseq_b in
  let to_ante_b = List.combine labels to_ante_f in
  (*t evars = explicitly_quantified @ evars in*)

  (*TODO: wrap implicit vars for to_ante
    (i) find FV=free vars of to_ante; (ii) select ctrs connected to FV (iii) remove redundant exists vars
  *)

  Debug.devel_pprint ("split_universal: evars: "
  ^ (String.concat ", "
	  (List.map Cprinter.string_of_spec_var evars))) pos;
  Debug.devel_pprint ("split_universal: expl_inst_vars: "
  ^ (String.concat ", "
	  (List.map Cprinter.string_of_spec_var expl_inst_vars))) pos;
  Debug.devel_pprint ("split_universal: vvars: "
  ^ (String.concat ", "
	  (List.map Cprinter.string_of_spec_var vvars))) pos;
  Debug.devel_pprint ("split_universal: to_ante: "
  ^ (Cprinter.string_of_pure_formula_branches (to_ante, to_ante_b))) pos;
  Debug.devel_pprint ("split_universal: to_conseq: "
  ^ (Cprinter.string_of_pure_formula_branches (to_conseq, to_conseq_b))) pos;
  let fvars = CP.fv f in

  (* 27.05.2008 *)
  if !Globals.move_exist_to_LHS & (not(Gen.is_empty (Gen.BList.difference_eq CP.eq_spec_var fvars evars)) & not(Gen.is_empty evars))	then
	(* there still are free vars whose bondings were not moved to the LHS --> existentially quantify the whole formula and move it to the LHS *)
	(* Ex.:  ex e. f1<e & e<=g or ex e. (f=1 & e=2 \/ f=2 & e=3) *)
	(*let _ = print_string("\n[solver.ml, split_universal]: No FV in  " ^ (Cprinter.string_of_pure_formula f) ^ "\n") in*)
	(* Branches not handled here yet *)
    let new_f = discard_uninteresting_constraint f vvars in
    (((CP.mkAnd to_ante (CP.mkExists evars new_f None pos) pos), []), (to_conseq, to_conseq_b), evars)
  else ((to_ante, to_ante_b), (to_conseq, to_conseq_b), evars)


(**************************************************************)
(**************************************************************)
(**************************************************************)
(*
  We do a simplified translation towards CNF where we only take out the common
  conjuncts from all the disjuncts:

  Ex:
  (a=1 & b=1) \/ (a=2 & b=2) - nothing common between the two disjuncts
  (a=1 & b=1 & c=3) \/ (a=2 & b=2 & c=3) ->  c=3 & ((a=1 & b=1) \/ (a=2 & b=2))
*)

(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*17.04.2009*)

and memo_normalize_to_CNF_n1 (f:MCP.memo_pure) pos : MCP.memo_pure = 
  List.map (fun c-> {c with MCP.memo_group_slice = List.map (fun c-> normalize_to_CNF_new c pos) c.MCP.memo_group_slice}) f

and memo_normalize_to_CNF_new (f:MCP.mix_formula) pos : MCP.mix_formula = match f with
  | MCP.MemoF f-> MCP.MemoF (memo_normalize_to_CNF_n1 f pos)
  | MCP.OnePF f -> MCP.OnePF (normalize_to_CNF_new f pos)

and normalize_to_CNF_new (f : CP.formula) pos : CP.formula = 
  let disj_list = (CP.list_of_disjs) f in
  let dc_list = List.map CP.list_of_conjs disj_list in
  match dc_list with
    | conj_list :: rest -> 
          let first_disj, res_conj, res_disj_list = (filter_common_conj conj_list rest pos) in
          let res_disj = List.map (fun c -> (CP.conj_of_list c pos)) res_disj_list in
          (CP.mkAnd (CP.conj_of_list res_conj pos) (CP.mkOr (CP.conj_of_list first_disj pos) (CP.disj_of_list res_disj pos) None pos) pos)
    | [] -> (print_string("[solver.ml, normalize_to_CNF]: should not be here!!"); (CP.mkTrue pos)) 

and filter_common_conj (conj_list : CP.formula list) (dc_list : (CP.formula list) list) pos : (CP.formula list *  CP.formula list * (CP.formula list list)) = 
  match conj_list with
    | h :: rest -> 
          let b, new_dc_list = remove_conj_list dc_list h pos in
          if b then 
	        let first_disj, conj, new_dc_list2 = filter_common_conj rest new_dc_list pos in
	        (first_disj, h::conj, new_dc_list2)
          else
	        let first_disj, conj, new_dc_list2 = filter_common_conj rest dc_list pos in
	        (h::first_disj, conj, new_dc_list2)
    | [] -> ([], [], dc_list)	

and remove_conj_list (f : (CP.formula list) list) (conj : CP.formula) pos : (bool * (CP.formula list list)) = match f with
  | h :: rest ->
        let b1, l1 = remove_conj_new h conj pos in
        let b2, l2 = remove_conj_list rest conj pos in
        (b1 & b2, l1::l2)
  | [] -> (true, [])		

and remove_conj_new (f : CP.formula list) (conj : CP.formula) pos : (bool * CP.formula list) = match f with
  | h :: rest -> 
        if (CP.eq_pure_formula h conj) then (true, rest)
        else
          let b1, l1 = remove_conj_new rest conj pos in (b1, h::l1)
  | [] -> (false, [])			

(*17.04.2009*)	
(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)

and normalize_to_CNF (f : CP.formula) pos : CP.formula = match f with
  | CP.Or (f1, f2, lbl, p) ->
        let conj, disj1, disj2 = (find_common_conjs f1 f2 p) in
	    (*
	      let _ = (print_string ("\n[cpure.ml, normalize_to_CNF]: f1: " ^ (Cprinter.string_of_pure_formula f1) ^ "\n")) in
	      let _ = (print_string ("\n[cpure.ml, normalize_to_CNF]: f2: " ^ (Cprinter.string_of_pure_formula f2) ^ "\n")) in
	      let _ = (print_string ("\n[cpure.ml, normalize_to_CNF]: Conj: " ^ (Cprinter.string_of_pure_formula conj) ^ "\n")) in
	      let _ = (print_string ("\n[cpure.ml, normalize_to_CNF]: disj1: " ^ (Cprinter.string_of_pure_formula disj1) ^ "\n")) in
	      let _ = (print_string ("\n[cpure.ml, normalize_to_CNF]: disj2: " ^ (Cprinter.string_of_pure_formula disj2) ^ "\n")) in
	    *)
        (CP.mkAnd conj (CP.mkOr disj1 disj2 lbl p) p)
  | CP.And (f1, f2, p) -> CP.mkAnd (normalize_to_CNF f1 p) (normalize_to_CNF f2 p) p
  | CP.Not (f1, lbl, p) -> CP.Not(normalize_to_CNF f1 p, lbl ,p)
  | CP.Forall (sp, f1, lbl, p) -> CP.Forall(sp, normalize_to_CNF f1 p, lbl ,p)
  | CP.Exists (sp, f1, lbl, p) -> CP.Exists(sp, normalize_to_CNF f1 p, lbl ,p)
  | _ -> f

(* take two formulas f1 and f2 and returns:
   - the formula containing the commom conjuncts
   - the formula representing what's left of f1
   - the formula representing what's left of f2
*)

and find_common_conjs (f1 : CP.formula) (f2 : CP.formula) pos : (CP.formula * CP.formula * CP.formula) = match f1 with
  | CP.BForm(b,_) ->
        if (List.exists (fun c -> (CP.eq_pure_formula c f1)) (CP.list_of_conjs f2)) then
          begin
	        (f1, (CP.mkTrue pos), (remove_conj f2 f1 pos))
          end
        else
	      (*
	        let _ = (print_string ("\n[cpure.ml, find_common_conjs]: no common conj between: \n")) in
	        let _ = (print_string ("\t\t " ^ (Cprinter.string_of_pure_formula f1) ^ "\n")) in
	        let _ = (print_string ("\t\t " ^ (Cprinter.string_of_pure_formula f2) ^ "\n")) in
	        let _ = (print_string ("\n[cpure.ml, find_common_conjs]: list of conj for f2: " ^ (Cprinter.string_of_pure_formula_list (CP.list_of_conjs f2)) ^ "\n")) in
	      *)
          ((CP.mkTrue pos), f1, f2)
  | CP.And(f11, f12, p) ->
        let outer_conj, new_f1, new_f2 = (find_common_conjs f11 f2 p) in
        let outer_conj_prim, new_f1_prim, new_f2_prim  = (find_common_conjs f12 new_f2 p) in
        ((CP.mkAnd outer_conj outer_conj_prim p), (CP.mkAnd new_f1 new_f1_prim p), new_f2_prim)
  | CP.Or(f11, f12, lbl ,p) ->
        let new_f11 = (normalize_to_CNF f11 p) in
        let new_f12 = (normalize_to_CNF f12 p) in
        (CP.mkTrue pos),(CP.mkOr new_f11 new_f12 lbl p),f2
  | _ -> ((CP.mkTrue pos), f1, f2)

and remove_conj (f : CP.formula) (conj : CP.formula) pos : CP.formula = match f with
  | CP.BForm(b1,_) ->
        begin
          match conj with
	        |CP.BForm(b2,_) ->
	             if (CP.eq_b_formula_no_aset b1 b2) then
	               (CP.mkTrue pos)
	             else f
	        | _ -> f
        end
  | CP.And(f1, f2, p) ->
        (CP.mkAnd (remove_conj f1 conj p) (remove_conj f2 conj p) p)
  | CP.Not(f1, lbl, p) -> CP.Not((remove_conj f1 conj p), lbl, p)
  | _ -> f

(**************************************************************)
(**************************************************************)
(**************************************************************)

(* 21.05.2008 *)
(*
  Say we have three kinds of vars
  f - free, g - global (from the view definition), e - existential
  Assume, we have expression at the end of folding:
  E1(f,g) & E2(g) & E3(e,f,g)

  First action is to discard E2(g) which has already been proven

  (discard_uninteresting_constraint f vvars) only maintains those vars containing vvars, which are vars of interest
*)

and discard_uninteresting_constraint (f : CP.formula) (vvars: CP.spec_var list) : CP.formula = match f with
  | CP.BForm _ ->
        if CP.disjoint (CP.fv f) vvars then (CP.mkTrue no_pos)
        else f
  | CP.And(f1, f2, l) -> CP.mkAnd (discard_uninteresting_constraint f1 vvars) (discard_uninteresting_constraint f2 vvars) l
  | CP.Or(f1, f2, lbl, l) -> CP.mkOr (discard_uninteresting_constraint f1 vvars) (discard_uninteresting_constraint f2 vvars) lbl  l
  | CP.Not(f1, lbl, l) -> CP.Not(discard_uninteresting_constraint f1 vvars, lbl, l)
  | _ -> f

and fold_op p c vd v pr u loc =
  Gen.Profiling.no_2 "fold" (fold_op_x(*debug_2*) p c vd v pr) u loc

(* and fold_debug_2 p c vd v u loc =  *)
(*   Gen.Debug.no_2 "fold_op " (fun c -> match c with *)
(*     | Ctx c -> Cprinter.string_of_formula c.es_formula *)
(*     | _ -> "CtxOR!")  *)
(*       Cprinter.string_of_h_formula  *)
(*       (fun (c,_) -> match c with | FailCtx _ -> "Fail" | _ -> "Success") *)
(*       (fun c v -> fold_op_x p c v u loc) c v *)

(* and fold_debug p c v u loc =  *)
(*   Gen.Debug.no_2 "fold_op " Cprinter.string_of_context Cprinter.string_of_h_formula (fun (c,_) -> Cprinter.string_of_list_context c) *)
(*       (fun c v -> fold_op_x p c v u loc) c v *)
(**************************************************************)
(**************************************************************)
(**************************************************************)

(* fold some constraints in ctx to view  *)
and fold_op_x prog (ctx : context) (view : h_formula) vd (* (p : CP.formula) *) prx (use_case:bool) (pos : loc): (list_context * proof) =
  let pr (x,_) = Cprinter.string_of_list_context x in
  let id x = x in
  let ans = ("use-case : "^string_of_bool use_case)^"\n context:"^(Cprinter.string_of_context ctx)^"\n rhs:"^(Cprinter.string_of_h_formula view) in
  let pr2 x = match x with 
    | None -> "None"
    | Some f -> Cprinter.string_of_struc_formula f.view_formula in
  Gen.Debug.no_2 "fold_op" 
      pr2 id pr
      (fun _ _ -> fold_op_x1  prog (ctx : context) (view : h_formula) vd (* (p : CP.formula) *) prx (use_case:bool) (pos : loc)) vd ans


and fold_op_x1 prog (ctx : context) (view : h_formula) vd (* (p : CP.formula) *) pr (use_case:bool) (pos : loc): (list_context * proof) = match view with
  | ViewNode ({ h_formula_view_node = p;
    h_formula_view_name = c;
    h_formula_view_imm = imm;
    h_formula_view_label = pid;
    h_formula_view_remaining_branches = r_brs;
	h_formula_view_perm = r_prm;
    h_formula_view_arguments = vs}) -> begin
      try
        let vdef = match vd with 
          | None -> look_up_view_def_raw prog.Cast.prog_view_decls c 
          | Some vd -> vd in
        (* is there a benefit for using case-construct during folding? *)
        let brs = filter_branches r_brs vdef.Cast.view_formula in
        (* let form = if use_case then brs else Cformula.case_to_disjunct brs in*)
        let form = Cformula.case_to_disjunct brs in
        let renamed_view_formula = rename_struc_bound_vars form in
	    (****)  
        let renamed_view_formula = 
	      if imm then 
	        Cformula.propagate_imm_struc_formula renamed_view_formula 
	      else
	        renamed_view_formula
        in 
	    (***)

        let fr_vars = (CP.SpecVar (Named vdef.Cast.view_data_name, self, Unprimed)):: vdef.view_vars in
        let to_vars = p :: vs in
        let view_form = subst_struc_avoid_capture fr_vars to_vars renamed_view_formula in
		let view_form = set_perm_struc view_form pr r_prm in
		(*let nvs = match r_prm with | None -> vs | Some v-> v::vs in*)
        let view_form = add_struc_origins view_form (get_view_origins view) in
        let view_form = CF.replace_struc_formula_label pid view_form in
        Debug.devel_pprint ("do_fold: LHS ctx:" ^ (Cprinter.string_of_context_short ctx)) pos;
        Debug.devel_pprint ("do_fold: RHS view: " ^ (Cprinter.string_of_h_formula view)) pos;
        Debug.devel_pprint ("do_fold: view_form: " ^ (Cprinter.string_of_struc_formula view_form)) pos;
        let estate = estate_of_context ctx pos in
		let ngen,nvs = match r_prm with | None -> estate.es_gen_impl_vars,vs | Some v -> (v::estate.es_gen_impl_vars,v::vs) in 
        let new_es = {estate with es_evars = nvs (*Gen.BList.remove_dups_eq (=) (vs @ estate.es_evars)*);  es_gen_impl_vars = ngen} in
        let new_ctx = Ctx new_es in 
	    (*let new_ctx = set_es_evars ctx vs in*)
        let rs0, fold_prf = heap_entail_one_context_struc_nth "fold" prog true false new_ctx view_form pos None in
        (*let _ = print_string ("before fold: " ^ (Cprinter.string_of_context new_ctx)) in
          let _ = print_string ("after fold: " ^ (Cprinter.string_of_list_context rs0)) in*)
        let tmp_vars = p :: (estate.es_evars @ nvs) in
	    (**************************************)
	    (*        process_one 								*)
	    (**************************************)
        let rec process_one (ss:CF.steps) rs1  =
	      Debug.devel_pprint ("fold: rs1:\n"^ (Cprinter.string_of_context rs1)) pos;
	      match rs1 with
	        | OCtx (c1, c2) ->
		          (*
		            It is no longer safe to assume that rs will be conjunctive.
		            The recursive folding entailment call (via case splitting
		            for example) can turn ctx to a disjunctive one, hence making
		            rs disjunctive.
		          *)
		          let tmp1 = process_one (CF.add_to_steps ss "left OR 3 on ante") c1 in
		          let tmp2 = process_one (CF.add_to_steps ss "right OR 3 on ante") c2 in
		          let tmp3 = (mkOCtx tmp1 tmp2 pos) in
		          tmp3
	        | Ctx es ->
		          (* let es = estate_of_context rs pos in *)
                  let es = CF.overwrite_estate_with_steps es ss in
		          let w = Gen.BList.difference_eq CP.eq_spec_var  es.es_evars tmp_vars in
				  let (es_p, es_br, es_pr) = es.es_pure in
		          let tmp_pure = 
					let p,b = elim_exists_pure w (es_p,es_br) true pos in
					let pr = Cpr.elim_pr_exists1 w es_pr in
					(p,b,pr) in
		          let res_rs = Ctx {es with es_evars = estate.es_evars;
				      es_pure = tmp_pure; es_prior_steps = (ss @ es.es_prior_steps);} in
		          Debug.devel_pprint ("fold: context at beginning of fold: "
				  ^ (Cprinter.string_of_spec_var p) ^ "\n"
				  ^ (Cprinter.string_of_context ctx)) pos;
		          Debug.devel_pprint ("fold: context at end of fold: "
				  ^ (Cprinter.string_of_spec_var p) ^ "\n"
				  ^ (Cprinter.string_of_context res_rs)) pos;
		          Debug.devel_pprint ("fold: es.es_pure: "
				  ^ (Cprinter.string_of_mix_formula_branches_perm es.es_pure)) pos;
		          res_rs in
	    let res = match rs0 with
          | FailCtx _ -> rs0
          | SuccCtx l -> SuccCtx (List.map (process_one []) l) in
	    (res, fold_prf)
      with
	    | Not_found -> report_error no_pos ("fold: view def not found:"^c^"\n") 
    end
  | _ ->
        Debug.devel_pprint ("fold: second parameter is not a view: "
		^ (Cprinter.string_of_h_formula view)) pos;
        report_error no_pos ("fold: second parameter is not a view\n") 
	        (*([], Failure)*)

and process_fold_result prog is_folding estate (fold_rs0:list_context) p2 vs2 base2 pos : (list_context * proof list) =
  let pr1 = Cprinter.string_of_list_context_short in
  let pr2 x = pr1 (fst x) in
  Gen.Debug.no_1 "process_fold_result" pr1 pr2 (fun _ -> process_fold_result_x prog is_folding estate (fold_rs0:list_context) p2 vs2 base2 pos )  fold_rs0
      
and process_fold_result_x prog is_folding estate (fold_rs0:list_context) p2 vs2 base2 pos : (list_context * proof list) =
  let pure2 = base2.formula_base_pure in
  let resth2 = base2.formula_base_heap in
  let type2 = base2.formula_base_type in
  let branches2 = base2.formula_base_branches in
  let flow2 = base2.formula_base_flow in
  let perm2 = base2.formula_base_perm in
  let rec process_one_x (ss:CF.steps) fold_rs1 = match fold_rs1 with
    | OCtx (c1, c2) ->
	      let tmp1, prf1 = process_one_x (add_to_steps ss "left OR 4 in ante") c1 in
	      let tmp2, prf2 = process_one_x  (add_to_steps ss "right OR 4 in ante") c2 in
	      let tmp3 = or_list_context tmp1 tmp2 in
	      let prf3 = Prooftracer.mkOrLeft fold_rs1 (Base base2) [prf1; prf2] in 
	      (tmp3, prf3)
    | Ctx fold_es ->
          let fold_es = CF.overwrite_estate_with_steps fold_es ss in
		  let es_p,es_br, es_pr = fold_es.es_pure in
          let e_pure = MCP.fold_mem_lst (CP.mkTrue pos) true true es_p in
	      let (to_ante, to_ante_br), (to_conseq, to_conseq_br), new_evars = 
            split_universal (e_pure, es_br) fold_es.es_evars fold_es.es_gen_expl_vars fold_es.es_gen_impl_vars vs2 pos in
		  let to_ante_pr, to_conseq_pr, new_evars_pr = 
			Cpr.split_universal1 es_pr fold_es.es_evars fold_es.es_gen_expl_vars fold_es.es_gen_impl_vars vs2 pos in
		  let conseq_pr = Cpr.mkAnd perm2 to_conseq_pr pos in
	      let tmp_conseq = mkBase resth2 pure2 type2 flow2 conseq_pr branches2 pos in
	      let new_conseq = normalize tmp_conseq (CF.replace_branches to_conseq_br (formula_of_pure_N to_conseq pos)) pos in
	      let new_ante = normalize fold_es.es_formula (CF.replace_perm_formula (CF.replace_branches to_ante_br (formula_of_pure_N to_ante pos)) to_ante_pr) pos in
          let new_ante = filter_formula_memo new_ante false in
	      let new_consumed = fold_es.es_heap in
          let impl_vars = Gen.BList.intersect_eq CP.eq_spec_var vs2 (CP.fv to_ante) in
          let new_impl_vars = Gen.BList.difference_eq CP.eq_spec_var estate.es_gen_impl_vars impl_vars in        
	      (* let _ = print_string("new_consumed = " ^ (Cprinter.string_of_h_formula new_consumed) ^ "\n") in *)
	      let new_es = {estate with 
              es_heap = new_consumed;
              es_formula = new_ante;
              es_evars = new_evars@new_evars_pr;
              es_unsat_flag =false;
              es_gen_impl_vars = new_impl_vars;
              (* es_aux_conseq = CP.mkAnd estate.es_aux_conseq to_conseq pos *)} in
	      let new_ctx = (Ctx new_es) in
	      Debug.devel_pprint ("process_fold_result: new_ctx after folding: "
		  ^ (Cprinter.string_of_spec_var p2) ^ "\n"
		  ^ (Cprinter.string_of_context new_ctx)) pos;
	      Debug.devel_pprint ("process_fold_result: vs2: "
		  ^ (String.concat ", "
			  (List.map Cprinter.string_of_spec_var vs2))) pos;
	      Debug.devel_pprint ("process_fold_result: to_ante: "
		  ^ (Cprinter.string_of_pure_formula to_ante)) pos;
	      Debug.devel_pprint ("process_fold_result: to_conseq: "
		  ^ (Cprinter.string_of_pure_formula to_conseq)) pos;
	      Debug.devel_pprint ("process_fold_result: new_conseq:\n"
		  ^ (Cprinter.string_of_formula new_conseq)) pos;
	      let rest_rs, prf = heap_entail_one_context prog is_folding new_ctx new_conseq pos
	      in
	      Debug.devel_pprint ("process_fold_result: context at end fold: "
		  ^ (Cprinter.string_of_spec_var p2) ^ "\n"
		  ^ (Cprinter.string_of_list_context rest_rs)) pos;
          let r = add_to_aux_conseq rest_rs to_conseq pos in
	      (r, prf) in
  let process_one (ss:CF.steps) fold_rs1 = 
    let pr1 = Cprinter.string_of_context  in
    let pr2 (c,_) = Cprinter.string_of_list_context c in
    Gen.Debug.no_1 "process_one" pr1 pr2 (fun _ -> process_one_x (ss:CF.steps) fold_rs1) fold_rs1 in
  match fold_rs0 with
    | FailCtx _ -> report_error no_pos ("process_fold_result: FailCtx encountered solver.ml\n")
    | SuccCtx fold_rs0 -> 
	      let t1,p1 = List.split (List.map (process_one []) fold_rs0) in
	      let t1 = fold_context_left t1 in
	      (t1,p1)       

(*added 09-05-2008 , by Cristian, checks that after the RHS existential elimination the newly introduced variables will no appear in the residue*)
and redundant_existential_check (svs : CP.spec_var list) (ctx0 : context) =
  match ctx0 with
    | Ctx es -> let free_var_list = (fv es.es_formula) in
	  begin if (not ( CP.disjoint svs free_var_list)) then
	    Debug.devel_pprint ("Some variable introduced by existential elimination where found in the residue") no_pos end
    | OCtx (c1, c2) ->
	      let _ = redundant_existential_check svs c1 in
	      (redundant_existential_check svs c2)

and elim_exists_pure w (f, b) lump pos =
  (elim_exists_mix_formula w f pos, List.map (fun (l, f) -> (l, elim_exists_pure_branch 3 w f pos)) b)

and elim_exists_mix_formula w f pos = match f with
  | MCP.MemoF f -> MCP.MemoF (elim_exists_memo_pure w f pos)
  | MCP.OnePF f -> MCP.OnePF (elim_exists_pure_branch 1 w f pos)

and elim_exists_memo_pure_x (w : CP.spec_var list) (f0 : MCP.memo_pure) pos =
  let f_simp w f pos = Gen.Profiling.push_time "elim_exists";
    let f_s = elim_exists_pure_branch 2(*_debug*) w f pos in
    Gen.Profiling.pop_time "elim_exists"; f_s in
  MCP.memo_pure_push_exists_all (f_simp,true) w f0 pos

and elim_exists_memo_pure(* _debug *) w f0 pos = 
  Gen.Debug.no_2 "elim_exists_memo_pure" Cprinter.string_of_spec_var_list Cprinter.string_of_memo_pure_formula Cprinter.string_of_memo_pure_formula
      (fun w f0 -> elim_exists_memo_pure_x w f0 pos) w f0

and elim_exists_pure_formula (f0:CP.formula) =
  match f0 with
    | CP.Exists _ ->
          (*let _ = print_string "***elim exists" in*)
          let sf=TP.simplify_a 11 f0 in
          sf
    | _ -> f0

and elim_exists_pure_formula_debug (f0:CP.formula) =
  Gen.Debug.no_1_opt (fun r -> not(r==f0)) "elim_exists_pure_formula" 
      Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula
      elim_exists_pure_formula f0


(* this method will lift out free conjuncts prior to an elimination
   of existential variables w that were newly introduced;
   r denotes that free variables from f0 that overlaps with w 
*)
and elim_exists_pure_branch (i:int) (w : CP.spec_var list) (f0 : CP.formula) pos : CP.formula =
  let pf = Cprinter.string_of_pure_formula in
  Gen.Debug.no_2 ("elim_exists_pure_branch"^(string_of_int i)) Cprinter.string_of_spec_var_list pf pf 
      (fun w f0 -> elim_exists_pure_branch_x w f0 pos) w f0

and elim_exists_pure_branch_x (w : CP.spec_var list) (f0 : CP.formula) pos : CP.formula =
  let r=if (w==[]) then [] else CP.intersect w (CP.fv f0) in
  if (r==[]) then f0
  else
    let lc = CP.split_conjunctions f0 in
    let (fl,bl)=List.partition (fun e -> CP.intersect r (CP.fv e)==[]) lc in
    let be = CP.join_conjunctions bl in 
    let f = CP.mkExists r be None pos in
    let sf = TP.simplify_a 2 f  in
    let simplified_f = List.fold_left (fun be e -> CP.mkAnd e be no_pos) sf fl in
    simplified_f

(* --- added 11.05.2008 *)
and entail_state_elim_exists es = 
  let f_prim = elim_exists es.es_formula in
  (* 05.06.08 *)
  (* we also try to eliminate exist vars for which a find a substitution of the form v = exp from the pure part *)
  (*let _ = print_string("[solver.ml, elim_exists_ctx]: Formula before exp exist elim: " ^ Cprinter.string_of_formula f_prim ^ "\n") in*)
  let f = elim_exists_exp f_prim in
  let qvar, base = CF.split_quantifiers f in
  let h, p, fl, pr, b, t = CF.split_components base in
  let simpl_p =	
    if !Globals.simplify_pure then 
      MCP.simpl_memo_pure_formula simpl_b_formula simpl_pure_formula p (TP.simplify_a 1)
    else p in
  let simpl_fl = fl (*flows have nothing to simplify to*)in
  let simpl_f = CF.mkExists qvar h simpl_p t simpl_fl pr b no_pos in
  Ctx{es with es_formula = simpl_f}   (*assuming no change in cache formula*)

and elim_exists_ctx_list (ctx0 : list_context) = 
  transform_list_context (entail_state_elim_exists, (fun c-> c)) ctx0

and elim_exists_partial_ctx_list (ctx0 : list_partial_context) = 
  transform_list_partial_context (entail_state_elim_exists, (fun c-> c)) ctx0

and elim_exists_failesc_ctx_list (ctx0 : list_failesc_context) = 
  transform_list_failesc_context (idf,idf,entail_state_elim_exists) ctx0

and elim_exists_ctx (ctx0:context) =
  transform_context entail_state_elim_exists ctx0

and elim_ante_evars (es:entail_state) : context = 
  let f = push_exists es.es_ante_evars es.es_formula in
  let ef = elim_exists f in
  Ctx {es with es_formula = ef } (*!! maybe unsound unless new clean cache id*)

(*used for finding the unsat in the original pred defs formulas*)
and find_unsat (prog : prog_decl) (f : formula):formula list*formula list =  
  let sat_subno = ref 1 in 
  match f with
    | Base _ | Exists _ ->
	      let _ = reset_int2 () in
	      let pf, pfb, _, _ = xpure prog f in

	      let is_ok =        
	        if pfb = [] then 
              TP.is_sat_mix_sub_no pf sat_subno true true
	        else
              (*  let r = TP.is_sat_mix_sub_no npf sat_subno true true in*)
              let npf = MCP.fold_mem_lst (CP.mkTrue no_pos) false true pf in
		      List.fold_left (fun is_ok (label, pf1b) ->
				  if not is_ok then false 
				  else TP.is_sat_sub_no (CP.And (npf, pf1b, no_pos)) sat_subno ) true pfb in	  
	      if is_ok then ([f],[]) else ([],[f])
    | Or ({formula_or_f1 = f1;
      formula_or_f2 = f2;
      formula_or_pos = pos}) ->
	      let nf1,nf1n = find_unsat prog f1 in
	      let nf2,nf2n = find_unsat prog f2 in
	      (nf1@nf2,nf1n@nf2n)

and is_unsat_with_branches xpure_f qvars hf mix pr br pos sat_subno=
  Gen.Debug.no_2 "is_unsat_with_branches" 
      (fun h -> (Cprinter.string_of_h_formula h)^"\n"^Cprinter.string_of_mix_formula(fst( xpure_f hf)))
      Cprinter.string_of_mix_formula string_of_bool
      (fun hf mix -> is_unsat_with_branches_x xpure_f qvars hf mix pr br pos sat_subno) hf mix

and is_unsat_with_branches_x xpure_f qvars hf mix pr br pos sat_subno=
  (* let wrap_exists f =  List.fold_left (fun a qv -> CP.Exists (qv, a, None, pos)) f qvars in*)
  if not (Cperm.is_sat pr) then true
  else
  let (ph, phb) = xpure_f hf in
  let phb = CP.merge_branches phb br in    
  if phb = [] then
    let npf = MCP.merge_mems mix ph true in
	(not (TP.is_sat_mix_sub_no npf sat_subno true true))
  else
    let npf = MCP.fold_mem_lst (MCP.fold_mem_lst (CP.mkTrue no_pos) false true ph) false true mix in
    let r = List.fold_left (fun is_ok (_,pf1b)->  
		is_ok  && (TP.is_sat_sub_no (CP.mkAnd npf pf1b no_pos) sat_subno)) 
      true phb in
	(not r)

and unsat_base_x prog (sat_subno:  int ref) f  : bool= 
  match f with
    | Or _ -> report_error no_pos ("unsat_xpure : encountered a disjunctive formula \n")
    | Base ({ formula_base_heap = h;
	  formula_base_pure = p;
	  formula_base_perm = pr;
	  formula_base_branches = br;
	  formula_base_pos = pos}) ->
          let pr_sol = Cpr.solve_once pr in
          is_unsat_with_branches (fun f-> let a,b,_,_ = xpure_heap 1 prog f 1 p pr_sol in (a,b)) [] h p pr br pos sat_subno
    | Exists ({ formula_exists_qvars = qvars;
      formula_exists_heap = qh;
      formula_exists_pure = qp;
	  formula_exists_perm = pr;
      formula_exists_branches = br;
      formula_exists_pos = pos}) ->
          let pr_sol = Cpr.solve_once pr in
          is_unsat_with_branches (fun f-> let a,b,_,_ = xpure_heap 1 prog f 1 qp pr_sol in (a,b)) qvars qh qp pr br pos sat_subno

and unsat_base_nth(*_debug*) n prog (sat_subno:  int ref) f  : bool = 
  (*unsat_base_x prog sat_subno f*)
  Gen.Debug.no_1 "unsat_base" 
      Cprinter.string_of_formula string_of_bool
      (fun _ -> unsat_base_x prog sat_subno f) f
      

and elim_unsat_es (prog : prog_decl) (sat_subno:  int ref) (es : entail_state) : context =
  let pr1 = Cprinter.string_of_entail_state in
  let pr2 = Cprinter.string_of_context in
  Gen.Debug.no_1 "elim_unsat_es" pr1 pr2 (fun _ -> elim_unsat_es_x prog sat_subno es) es
      
and elim_unsat_es_x (prog : prog_decl) (sat_subno:  int ref) (es : entail_state) : context =
  if (es.es_unsat_flag) then Ctx es
  else elim_unsat_es_now prog sat_subno es

and elim_unsat_es_now (prog : prog_decl) (sat_subno:  int ref) (es : entail_state) : context =
  let f = es.es_formula in
  let _ = reset_int2 () in
  let b = unsat_base_nth "1" prog sat_subno f in
  if not b then Ctx{es with es_unsat_flag = true } else 
	false_ctx (flow_formula_of_formula es.es_formula) no_pos

and elim_unsat_for_unfold (prog : prog_decl) (f : formula) : formula= match f with
  | Or _ -> elim_unsat_all prog f 
  | _ -> f

and elim_unsat_all prog (f : formula): formula = match f with
  | Base _ | Exists _ ->
        let sat_subno = ref 1 in	
        let _ = reset_int2 () in
	    (*(*      print_endline (Cprinter.string_of_formula f);*)
          let pf, pfb = xpure prog f in
          let is_ok =
          if pfb = [] then 
          let f_lst = MCP.fold_mix_lst_to_lst pf false true true in
          List.fold_left (fun a c-> if not a then a else TP.is_sat_sub_no c sat_subno) true f_lst 
	      else
          let npf = MCP.fold_mem_lst (CP.mkTrue no_pos) false true pf in
	      List.fold_left (fun is_ok (label, pf1b) ->
          if not is_ok then false 
          else TP.is_sat_sub_no (CP.And (npf, pf1b, no_pos)) sat_subno ) true pfb in
	      TP.incr_sat_no ();
	    (*      if is_ok then print_endline "elim_unsat_all: true" else print_endline "elim_unsat_all: false";*)*)
        let is_ok = unsat_base_nth "2" prog sat_subno f in
	    if not is_ok then f else mkFalse (flow_formula_of_formula f) (pos_of_formula f)
  | Or ({ formula_or_f1 = f1;
	formula_or_f2 = f2;
	formula_or_pos = pos}) ->
        let nf1 = elim_unsat_all prog f1 in
        let nf2 = elim_unsat_all prog f2 in
	    mkOr nf1 nf2 pos


and elim_unsat_all_debug prog (f : formula): formula = 
  Gen.Debug.no_2 "elim_unsat " (fun c-> "?") (Cprinter.string_of_formula) (Cprinter.string_of_formula) elim_unsat_all prog f

and get_eqns_free (st : ((CP.spec_var * CP.spec_var) * branch_label) list) (evars : CP.spec_var list) (expl_inst : CP.spec_var list) 
      (struc_expl_inst : CP.spec_var list) pos : (CP.formula * (branch_label * CP.formula) list)*(CP.formula * (branch_label * CP.formula) list)*
      (CP.spec_var * CP.spec_var) list = 
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr_p =  Cprinter.string_of_pure_formula in
  let pr_st l  = pr_list (fun (c,_)-> pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var c) l in
  let pr_st2 l  = pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) l in
  let pr ((lhs,_),(rhs,_),s) = (pr_pair pr_p pr_p (lhs,rhs))^"subst:"^(pr_st2 s) in
  Gen.Debug.no_3 "get_eqns_free" pr_st pr_svl pr_svl  pr (fun _ _ _ -> get_eqns_free_x (st : ((CP.spec_var * CP.spec_var) * branch_label) list) (evars : CP.spec_var list) (expl_inst : CP.spec_var list) 
      (struc_expl_inst : CP.spec_var list) pos) st evars expl_inst

(* extracts those involve free vars from a set of equations  - here free means that it is not existential and it is not meant for explicit instantiation *)
(*NOTE: should (fr,t) be added for (CP.mem fr expl_inst)*)
and get_eqns_free_x (st : ((CP.spec_var * CP.spec_var) * branch_label) list) (evars : CP.spec_var list) (expl_inst : CP.spec_var list) 
      (struc_expl_inst : CP.spec_var list) pos : (CP.formula * (branch_label * CP.formula) list)*(CP.formula * (branch_label * CP.formula) list)*
      (CP.spec_var * CP.spec_var) list = 
  match st with
    | ((fr, t), br_label) :: rest ->
	      let ((rest_left_eqns, rest_left_eqns_br),(rest_right_eqns, rest_right_eqns_br),s_list) = get_eqns_free_x rest evars expl_inst struc_expl_inst pos in
	      if (CP.mem fr evars) || (CP.mem fr expl_inst)  (*TODO: should this be uncommented? || List.mem t evars *) then
	        ((rest_left_eqns, rest_left_eqns_br),(rest_right_eqns, rest_right_eqns_br),(fr, t)::s_list)
	      else if (CP.mem fr struc_expl_inst) then
	        let tmp = CP.mkEqVar fr t pos in
		    if br_label = "" then
		      let res = CP.mkAnd tmp rest_right_eqns pos in
		      ((rest_left_eqns, rest_left_eqns_br),(res, rest_right_eqns_br),s_list)
		    else
		      ((rest_left_eqns, rest_left_eqns_br),(rest_right_eqns, CP.add_to_branches br_label tmp rest_right_eqns_br),s_list)
	      else
	        let tmp = CP.mkEqVar fr t pos in
		    if br_label = "" then
		      let res = CP.mkAnd tmp rest_left_eqns pos in
		      ((res, rest_left_eqns_br),(rest_right_eqns, rest_right_eqns_br),s_list)
		    else
		      ((rest_left_eqns, CP.add_to_branches br_label tmp rest_left_eqns_br),(rest_right_eqns, rest_right_eqns_br),s_list)
    | [] -> ((CP.mkTrue pos, []),(CP.mkTrue pos, []),[])

(*
  ivar -> tvar (tvar in impl_var);
  expl_var += {ivar}
  evar -= {tvar}
  impl_var -= {tvar}
  ivar -> tvar (tvar in expl_var);
  ivar -> tvar (tvar in evar)

  returns  [(tvar->ivar)] [fvar->tvar]
*)

and subs_to_inst_vars (st : ((CP.spec_var * CP.spec_var) * branch_label) list) (ivars : CP.spec_var list) 
      (impl_vars: CP.spec_var list) pos 
      : (( CP.spec_var list * CP.spec_var list * (CP.spec_var * CP.spec_var) list) *   ((CP.spec_var * CP.spec_var)* branch_label) list) =
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr_sv = Cprinter.string_of_spec_var in
  let pr_subs xs = pr_list (pr_pair pr_sv pr_sv) xs in
  (* let pr_lf xs = pr_list Cprinter.string_of_pure_formula xs in *)
  let pr2 xs = pr_list (fun (c,_) -> pr_pair pr_sv pr_sv c) xs in
  let pr_r ((l1,l2,s1),s2)  = "("^(pr_svl l1)^","^(pr_svl l2)^","^(pr_subs s1)^","^(pr2 s2)^")" in
  Gen.Debug.no_2 "subs_to_inst_vars" pr2 pr_svl pr_r (fun _ _ -> subs_to_inst_vars_x st ivars impl_vars pos) st ivars 

and subs_to_inst_vars_x (st : ((CP.spec_var * CP.spec_var) * branch_label) list) (ivars : CP.spec_var list) 
      (impl_vars: CP.spec_var list) pos 
      : (( CP.spec_var list * CP.spec_var list * (CP.spec_var * CP.spec_var) list) *   ((CP.spec_var * CP.spec_var)* branch_label) list) =
  let rec helper st nsubs iv impl_v = match st with
    | ((rv, lv),_) :: rest ->
          let f = helper rest ((lv,rv)::nsubs) (lv::iv) in
          if (CP.mem rv impl_vars) then
            f (rv::impl_v)  
          else (* t in ex_vars || t in expl_vars *)
            f impl_v 
    | [] -> (impl_v,iv,nsubs) in 
  (* impl_v to subtract from e_var and add to expl_var *) 
  let (i_st, r_st) = List.partition (fun ((_,lv),_) -> CP.mem lv ivars) st  in
  (helper i_st [] [] [] ,r_st)

(*
  - extract the equations for the variables that are to be explicitly instantiated
  - remove the variables already instantiated from ivars
  - expl_vars will contain the vars that are next to be explicitly instantiated: for each equation ivar = v, it adds v to the list of vars that will be explicitly instantiated later
*)
and get_eqns_expl_inst_x (st : (CP.spec_var * CP.spec_var) list) (ivars : CP.spec_var list) (*(expl_vars : CP.spec_var list) *)pos 
      : (CP.formula list * CP.spec_var list (*remaining ivar*) * CP.spec_var list) = 
  let rec helper st ivars = match st with
    | (fr, t) :: rest ->
          if (CP.mem fr ivars) then
	        let ivars' = (List.filter (fun x -> not(CP.eq_spec_var fr x)) ivars) in
	        let (rest_eqns, ivars_new, expl_vars_new) = helper rest ivars' in
	        let tmp = CP.mkEqVar fr t pos in
	        let res = [tmp]@rest_eqns in
	        (*let _ = print_string ("expl_inst: " ^ (Cprinter.string_of_pure_formula tmp) ^ "\n") in*)
	        (res, ivars_new, t::expl_vars_new)
          else (
	          if (CP.mem t ivars) then
	            let ivars' = (List.filter (fun x -> not(CP.eq_spec_var t x)) ivars) in
	            let (rest_eqns, ivars_new, expl_vars_new) = helper  rest ivars'  in
	            let tmp = CP.mkEqVar t fr pos in
	            let res = [tmp]@rest_eqns in
	            (*let _ = print_string ("expl_inst: " ^ (Cprinter.string_of_pure_formula tmp) ^ "\n") in*)
	            (res, ivars_new, fr::expl_vars_new)
	          else
	            (helper  rest ivars)
          )
    | [] -> ([], ivars, [])
  in helper st ivars

and get_eqns_expl_inst (st : (CP.spec_var * CP.spec_var) list) (ivars : CP.spec_var list) (*(expl_vars : CP.spec_var list) *)pos : (CP.formula list * CP.spec_var list * CP.spec_var list) = 
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr_lf xs = pr_list Cprinter.string_of_pure_formula xs in
  let pr_r (lf,l1,l2)  = "("^(pr_lf lf)^","^(pr_svl l1)^","^(pr_svl l2)^")" in
  let pr_sv = Cprinter.string_of_spec_var in
  let pr2 xs = pr_list (pr_pair pr_sv pr_sv) xs in
  Gen.Debug.no_2 "get_eqns_expl_inst" pr2 pr_svl pr_r (fun _ _ -> get_eqns_expl_inst_x st ivars pos) st ivars 




(* removing existentail using ex x. (x=y & P(x)) <=> P(y) *)
and elim_pure_exists (f0 : formula) : formula = match f0 with
  | Or ({ formula_or_f1 = f1;
    formula_or_f2 = f2;
    formula_or_pos = pos}) ->
        let ef1 = elim_pure_exists f1 in
        let ef2 = elim_pure_exists f2 in
	    mkOr ef1 ef2 pos
  | Base _ -> f0
  | Exists ({ formula_exists_qvars = qvar :: rest_qvars;
    formula_exists_heap = h;
    formula_exists_pure = p;
    formula_exists_type = t;
    formula_exists_flow = fl;
	formula_exists_perm = pr;
    formula_exists_branches = b;
    formula_exists_pos = pos}) ->
        let st, pp1 = MCP.get_subst_equation_memo_formula_vv p qvar in
        let r = if List.length st = 1 then
          let tmp = mkBase h pp1 t fl pr b pos in
          let new_baref = subst st tmp in
          let tmp2 = add_quantifiers rest_qvars new_baref in
          let tmp3 = elim_pure_exists tmp2 in
          tmp3
        else (* if qvar is not equated to any variables, try the next one *)
          let tmp1 = mkExists rest_qvars h p t fl pr b pos in
          let tmp2 = elim_pure_exists tmp1 in
          let tmp3 = add_quantifiers [qvar] tmp2 in
          tmp3 in
        r
  | Exists _ -> report_error no_pos ("Solver.elim_pure_exists: Exists with an empty list of quantified variables")
  
and elim_exists (f0:formula) : formula = 
 let rec helper f0 = match f0 with
  | Or ({ formula_or_f1 = f1;formula_or_f2 = f2;formula_or_pos = pos}) -> mkOr (helper f1) (helper f2) pos
  | Base _ -> f0
  | Exists e->
        let hfv = h_fv e.formula_exists_heap in
        let l2,l1 = List.partition (fun v-> List.exists (CP.eq_spec_var v) hfv) e.formula_exists_qvars in
        let rqv, pp1 = Cperm.elim_exists_perm l1 e.formula_exists_perm in
			mkExists (rqv@l2) e.formula_exists_heap e.formula_exists_pure e.formula_exists_type e.formula_exists_flow pp1 e.formula_exists_branches e.formula_exists_pos in 
   elim_pure_exists (helper f0)   
	 

(**************************************************************)
(* heap entailment                                            *)
(**************************************************************)

and filter_set (cl : list_context) : list_context =
  if !Globals.use_set  then cl
  else match cl with 
    | FailCtx _ -> cl
    | SuccCtx l -> if Gen.is_empty l then cl else SuccCtx [(List.hd l)]
	    (* setup the labeling in conseq and the fail context in cl *)

and heap_entail_failesc_prefix_init (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_failesc_context)
      (conseq : 'a) pos (pid:control_path_id) ((rename_f: 'a->'a), (to_string:'a->string),
	  (f: prog_decl->bool->bool->context->'a -> loc ->control_path_id->(list_context * proof))
	  ) : (list_failesc_context * proof) = 
  (* if (List.length cl)<1 then report_error pos ("heap_entail_failesc_prefix_init : encountered an empty list_partial_context \n") *)
  (* else *)
  (* TODO : must avoid empty context *)
  if (cl==[]) then ([],UnsatAnte)
  else
    begin
      reset_formula_point_id();
      let rename_es es = {es with es_formula = rename_labels_formula_ante es.es_formula}in
      let conseq = rename_f conseq in
      let rec prepare_ctx es = {es with 
		  es_success_pts  = ([]: (formula_label * formula_label)  list)  ;(* successful pt from conseq *)
		  es_residue_pts  = residue_labels_in_formula es.es_formula ;(* residue pts from antecedent *)
		  es_id      = (fst (fresh_formula_label ""))              ; (* unique +ve id *)
		  es_orig_ante   = es.es_formula;
		  (*es_orig_conseq = conseq ;*)}in	
      let cl_new = transform_list_failesc_context (idf,idf,(fun es-> Ctx(prepare_ctx (rename_es (reset_original_es es))))) cl in
      let entail_fct = fun c-> heap_entail_struc_list_failesc_context prog is_folding  has_post c conseq pos pid f to_string in 
      heap_entail_agressive_prunning entail_fct (*(prune_ctx_failesc_list prog)*) (fun a->a) (fun (c,_) -> isSuccessListFailescCtx c) cl_new
    end

and heap_entail_prefix_init (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_partial_context)
      (conseq : 'a) pos (pid:control_path_id) ((rename_f: 'a->'a), (to_string:'a->string),
	  (f: prog_decl->bool->bool->context->'a -> loc ->control_path_id->(list_context * proof)))
      : (list_partial_context * proof) = 
  if (List.length cl)<1 then report_error pos ("heap_entail_prefix_init : encountered an empty list_partial_context \n")
  else
    (* if cl==[] then (cl,UnsatAnte) *)
    (* else  *)
    begin
      reset_formula_point_id();
      let rename_es es = {es with es_formula = rename_labels_formula_ante es.es_formula}in
      let conseq = rename_f conseq in
      let rec prepare_ctx es = {es with 
		  es_success_pts  = ([]: (formula_label * formula_label)  list)  ;(* successful pt from conseq *)
		  es_residue_pts  = residue_labels_in_formula es.es_formula ;(* residue pts from antecedent *)
		  es_id      = (fst (fresh_formula_label ""))              ; (* unique +ve id *)
		  es_orig_ante   = es.es_formula;
		  (*es_orig_conseq = conseq ;*)}in	
      let cl_new = transform_list_partial_context ((fun es-> Ctx(prepare_ctx (rename_es es))),(fun c->c)) cl in
      heap_entail_struc_list_partial_context prog is_folding  has_post cl_new conseq pos pid f to_string
    end

and heap_entail_struc_list_partial_context (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_partial_context)
      (conseq:'a) pos (pid:control_path_id) (f: prog_decl->bool->bool->context->'a -> loc
                                              ->control_path_id->(list_context * proof)) to_string : (list_partial_context * proof) =           
  (* print_string ("\ncalling struct_list_partial_context .."^string_of_int(List.length cl)); *)
  (* print_string (Cprinter.string_of_list_partial_context cl); *)
  Debug.devel_pprint ("heap_entail_struc_list_partial_context:"
  ^ "\nctx:\n" ^ (Cprinter.string_of_list_partial_context cl)
  ^ "\nconseq:\n" ^ (to_string conseq)) pos; 
    let l = List.map 
      (fun c-> heap_entail_struc_partial_context prog is_folding  has_post c conseq pos pid f to_string) cl in
    let l_ctx , prf_l = List.split l in
    let result = List.fold_left list_partial_context_union (List.hd l_ctx) (List.tl l_ctx) in
    let proof = ContextList { 
        context_list_ante = [];
        context_list_conseq = struc_formula_of_formula (mkTrue (mkTrueFlow ()) pos) pos;
        context_list_proofs = prf_l; } in
    (result, proof)

and heap_entail_struc_list_failesc_context (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_failesc_context)
      (conseq) pos (pid:control_path_id) f to_string : (list_failesc_context * proof) =           
  Gen.Debug.no_1 "heap_entail_struc_list_failesc_context" (fun _ -> "?") (fun _ -> "?") 
      (fun _ -> heap_entail_struc_list_failesc_context_x prog is_folding  has_post cl 
          (conseq) pos pid f to_string) 0

and heap_entail_struc_list_failesc_context_x (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_failesc_context)
      (conseq) pos (pid:control_path_id) f to_string : (list_failesc_context * proof) =           
  (* print_string ("\ncalling struct_list_partial_context .."^string_of_int(List.length cl)); *)
  (* print_string (Cprinter.string_of_list_partial_context cl); *)
  let l = List.map 
    (fun c-> heap_entail_struc_failesc_context prog is_folding  has_post c conseq pos pid f to_string) cl in
  let l_ctx , prf_l = List.split l in
  let result = List.fold_left list_failesc_context_union (List.hd l_ctx) (List.tl l_ctx) in
  let proof = ContextList { 
      context_list_ante = [];
      context_list_conseq = struc_formula_of_formula (mkTrue (mkTrueFlow ()) pos) pos;
      context_list_proofs = prf_l; } in
  (result, proof)

and heap_entail_struc_partial_context (prog : prog_decl) (is_folding : bool) 
      (has_post: bool)(cl : partial_context) (conseq:'a) pos (pid:control_path_id) 
      (f: prog_decl->bool->bool->context->'a -> loc ->control_path_id->(list_context * proof)) to_string
      : (list_partial_context * proof) = 
  (* print_string "\ncalling struct_partial_context .."; *)
  Debug.devel_pprint ("heap_entail_struc_partial_context:"
  ^ "\nctx:\n" ^ (Cprinter.string_of_partial_context cl)
  ^ "\nconseq:\n" ^ (to_string conseq)) pos; 
    let fail_branches, succ_branches  = cl in
    let res = List.map (fun (lbl,c2)-> 
		(* print_string ("\nInput ==> :"^(Cprinter.string_of_context c2)); *)
		(* print_string ("\nConseq ==> :"^(to_string conseq)); *)
		let list_context_res,prf = f (*heap_entail_one_context_struc*) prog is_folding has_post c2 conseq pos pid in
		(* print_string ("\nOutcome ==> "^(Cprinter.string_of_list_context list_context_res)) ; *)
		let res = match list_context_res with
		  | FailCtx t -> [([(lbl,t)],[])]
		  | SuccCtx ls -> List.map ( fun c-> ([],[(lbl,c)])) ls in
		(res, prf)) succ_branches in
    let res_l,prf_l =List.split res in
    (* let n = string_of_int (List.length res) in *)
    (* print_string ("\nCombining ==> :"^n^" "^(Cprinter.string_of_list_list_partial_context res_l)); *)
    let res = List.fold_left list_partial_context_or [(fail_branches,[])] res_l in
    (* print_string ("\nResult of Combining ==> :"^(Cprinter.string_of_list_partial_context res)); *)
    let proof = ContextList { 
        context_list_ante = [];
        context_list_conseq = struc_formula_of_formula (mkTrue (mkTrueFlow ()) pos) pos;
        context_list_proofs = prf_l; } in
    (res, proof)

and heap_entail_struc_failesc_context (prog : prog_decl) (is_folding : bool) 
      (has_post: bool)(cl : failesc_context) (conseq:'a) pos (pid:control_path_id) f to_string: (list_failesc_context * proof) = 
  Gen.Debug.no_1 "heap_entail_struc_failesc_context" (fun _ -> "?") (fun _ -> "?") (fun x -> 
      heap_entail_struc_failesc_context_x prog is_folding
          (has_post)(cl) (conseq) pos (pid) f to_string) conseq


and heap_entail_struc_failesc_context_x (prog : prog_decl) (is_folding : bool) 
      (has_post: bool)(cl : failesc_context) (conseq:'a) pos (pid:control_path_id) f to_string: (list_failesc_context * proof) = 
  (* print_string "\ncalling struct_partial_context .."; *)
  Debug.devel_pprint ("heap_entail_struc_failesc_context:"
  ^ "\nctx:\n" ^ (Cprinter.string_of_failesc_context cl)
  ^ "\nconseq:\n" ^ (to_string conseq)) pos; 
    let fail_branches, esc_branches, succ_branches  = cl in
    let res = List.map (fun (lbl,c2)-> 
		(* print_string ("\nInput ==> :"^(Cprinter.string_of_context c2)); *)
		(* print_string ("\nConseq ==> :"^(to_string conseq)); *)
		let list_context_res,prf = f (*heap_entail_one_context_struc*) prog is_folding  has_post c2 conseq pos pid in
		(* print_string ("\nOutcome ==> "^(Cprinter.string_of_list_context list_context_res)) ; *)
		let res = match list_context_res with
		  | FailCtx t -> [([(lbl,t)],[],[])]
		  | SuccCtx ls -> List.map ( fun c-> ([],[],[(lbl,c)])) ls in
		(res, prf)) succ_branches in
    let res_l,prf_l =List.split res in
    (* print_string ("\nCombining ==> :"^(Cprinter.string_of_list_list_partial_context res_l)); *)
    let res = List.fold_left (list_failesc_context_or Cprinter.string_of_esc_stack) [(fail_branches,esc_branches,[])] res_l in
    (* print_string ("\nResult of Combining ==> :"^(Cprinter.string_of_list_partial_context res)); *)
    let proof = ContextList { 
        context_list_ante = [];
        context_list_conseq = struc_formula_of_formula (mkTrue (mkTrueFlow ()) pos) pos;
        context_list_proofs = prf_l; } in
    (res, proof)  

and heap_entail_struc_init (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_context) (conseq : struc_formula) pos (pid:control_path_id): (list_context * proof) = 
  Debug.devel_pprint ("heap_entail_struc_init:"
  ^ "\nctx:\n" ^ (Cprinter.string_of_list_context cl)
  ^ "\nconseq:\n" ^ (Cprinter.string_of_struc_formula conseq)) pos; 
    match cl with
      | FailCtx fr ->(cl,Failure)
      | SuccCtx _ ->
	        reset_formula_point_id();
	        let rename_es es = {es with es_formula = normalize_frac_formula prog (rename_labels_formula_ante es.es_formula)}in
	        let conseq = normalize_frac_struc prog (rename_labels_struc conseq) in
	        let rec prepare_ctx es = {es with 
                    es_success_pts  = ([]: (formula_label * formula_label)  list)  ;(* successful pt from conseq *)
                    es_residue_pts  = residue_labels_in_formula es.es_formula ;(* residue pts from antecedent *)
                    es_id      = (fst (fresh_formula_label ""))              ; (* unique +ve id *)
                    es_orig_ante   = es.es_formula;
                    es_orig_conseq = conseq ;}in	
	        let cl_new = transform_list_context ( (fun es-> Ctx(prepare_ctx (rename_es es))),(fun c->c)) cl in
            let entail_fct = fun c-> heap_entail_struc prog is_folding  has_post c conseq pos pid in
            let (ans,prf) = heap_entail_agressive_prunning entail_fct (*(prune_list_ctx prog)*) (fun a-> a) (fun (c,_)-> not (isFailCtx c)) cl_new in
            (CF.list_context_simplify ans,prf)

(* check entailment:                                          *)
(* each entailment should produce one proof, be it failure or *)
(* success. *)
and heap_entail_struc (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_context) (conseq : struc_formula) pos pid: (list_context * proof) =
  match cl with 
    | FailCtx _ -> (cl,Failure)
    | SuccCtx cl ->
	      if !Globals.use_set || Gen.is_empty cl then
	        let tmp1 = List.map (fun c -> heap_entail_one_context_struc_nth "4" prog is_folding  has_post c conseq pos pid) cl in
	        let tmp2, tmp_prfs = List.split tmp1 in
	        let prf = mkContextList cl conseq tmp_prfs in
            ((fold_context_left tmp2), prf)
	      else
	        (heap_entail_one_context_struc_nth "5" prog is_folding  has_post (List.hd cl) conseq pos pid)

and heap_entail_one_context_struc p i1 hp cl cs pos pid =
  Gen.Profiling.do_3 "heap_entail_one_context_struc" (heap_entail_one_context_struc_x(*_debug*) p i1 hp cl) cs pos pid

and heap_entail_one_context_struc_nth n p i1 hp cl cs pos pid =
  let str="heap_entail_one_context_struc" in
  Gen.Profiling.do_3_num n str (heap_entail_one_context_struc_y(*_debug*) p i1 hp cl) cs pos pid

and heap_entail_one_context_struc_y p i1 hp cl cs pos pid =
  let pr (x,_) = Cprinter.string_of_list_context x in
  Gen.Debug.no_2 "heap_entail_one_context_struc" Cprinter.string_of_context Cprinter.string_of_struc_formula pr 
    (fun cl _ -> heap_entail_one_context_struc_x p i1 hp cl cs pos pid) cl cs

and heap_entail_one_context_struc_x (prog : prog_decl) (is_folding : bool)  has_post (ctx : context) (conseq : struc_formula) pos pid : (list_context * proof) =
  Debug.devel_pprint ("heap_entail_one_context_struc:"
  ^ "\nctx:\n" ^ (Cprinter.string_of_context ctx)
  ^ "\nconseq:\n" ^ (Cprinter.string_of_struc_formula conseq)) pos;
    if isAnyFalseCtx ctx then
      (* check this first so that false => false is true (with false residual) *)
      ((SuccCtx [ctx]), UnsatAnte)
    else(* if isConstFalse conseq then
	       (--[], UnsatConseq)
	       else *)if isConstETrue conseq then
      ((SuccCtx [ctx]), TrueConseq)
    else
      (*let ctx = (*if !Globals.elim_unsat then elim_unsat_ctx prog ctx else *) (*elim_unsat_ctx prog *)ctx in
        if isAnyFalseCtx ctx then
        ([false_ctx pos], UnsatAnte)
        else*)
      let result, prf = heap_entail_after_sat_struc prog is_folding  has_post ctx conseq pos pid []  in
      (result, prf)

and heap_entail_after_sat_struc prog is_folding  has_post
      ctx conseq pos pid (ss:steps) : (list_context * proof) =     
  match ctx with
    | OCtx (c1, c2) ->
          Debug.devel_pprint ("heap_entail_after_sat_struc:"
		  ^ "\nctx:\n" ^ (Cprinter.string_of_context ctx)
		  ^ "\nconseq:\n" ^ (Cprinter.string_of_struc_formula conseq)) pos;
          let rs1, prf1 = heap_entail_after_sat_struc prog is_folding
            has_post c1 conseq pos pid (CF.add_to_steps ss "left OR 5 on ante") in
          let rs2, prf2 = heap_entail_after_sat_struc prog is_folding  has_post c2 conseq pos pid (CF.add_to_steps ss "right OR 5 on ante") in
	      ((or_list_context rs1 rs2),(mkOrStrucLeft ctx conseq [prf1;prf2]))
    | Ctx es -> begin
        Debug.devel_pprint ("heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc"
		^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx)
		^ "\nconseq:\n" ^ (Cprinter.string_of_struc_formula conseq)) pos;
        (*let es = {es with es_formula = prune_preds prog es.es_formula } in*)
        let es = (CF.add_to_estate_with_steps es ss) in
        let tmp, prf = heap_entail_conjunct_lhs_struc prog is_folding  has_post (Ctx es) conseq pos pid in
	    (filter_set tmp, prf)
      end

and sem_imply_add prog is_folding  ctx (p:CP.formula) only_syn:(context*bool) = match ctx with
  | OCtx _ -> report_error no_pos ("sem_imply_add: OCtx encountered \n")
  | Ctx c -> 
        if (CP.isConstTrue p) then (ctx,true)
        else
	      if (sintactic_search c.es_formula p) then (ctx,true)
	      else if only_syn then (print_string "only syn\n"; (ctx,false))
	      else
	        let b = (xpure_imply prog is_folding  c p !Globals.imply_timeout) in
	        if b then 
              ((Ctx {c with 
                  es_formula =(mkAnd_pure_and_branch 
				      c.es_formula 
				      (MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) p) 
				      [] 
				      no_pos)}),true)
	        else (ctx,false)


and syn_imply ctx p :bool = match ctx with
  | OCtx _ -> report_error no_pos ("syn_imply: OCtx encountered \n")
  | Ctx c -> 
	    if (sintactic_search c.es_formula p) then true
	    else false 

and count_octx x = match x with
  | OCtx (c1,c2) -> (count_octx c1) + (count_octx c2)
  | _ -> 1

and heap_entail_conjunct_lhs_struc
      p is_folding  has_post ctx conseq 
      pos pid : (list_context * proof) = 
  let pr x = match x with Ctx _ -> "Ctx " | OCtx _ -> ("OCtx "^(Cprinter.string_of_context_short x)) in
  Gen.Debug.no_2 "heap_entail_conjunct_lhs_struc"
      pr (Cprinter.string_of_struc_formula)
      (fun _ -> "?")
      (fun ctx conseq -> heap_entail_conjunct_lhs_struc_x p is_folding  has_post ctx conseq pos pid) ctx conseq

and heap_entail_conjunct_lhs_struc_x
      (prog : prog_decl) 
      (is_folding : bool) 
      
      (has_post:bool)
      (ctx_00 : context) 
      (conseq : struc_formula) pos pid : (list_context * proof) =


  let estate = match ctx_00 with
    | OCtx _ -> report_error no_pos ("heap_entail_conjunct_lhs_struc : OCtx encountered \n")
    | Ctx es -> es in


  (* and inner_entailer ctx conseq = *)
  (*   Gen.Debug.no_2 "inner_entailer" (Cprinter.string_of_context) (Cprinter.string_of_struc_formula) (fun (l,p) -> (Cprinter.string_of_list_context l)^"\nProof:"^(Prooftracer.string_of_proof p)) inner_entailer_a ctx conseq *)

  (* let rec inner_entailer_octx (ctx:context) (conseq:struc_formula) : (list_context * proof) =      *)
  (* match ctx with *)
  (*   | OCtx (c1, c2) -> *)
  (*         Debug.devel_pprint ("inner_entail_octx:" *)
  (*   	  ^ "\nctx:\n" ^ (Cprinter.string_of_context ctx) *)
  (*   	  ^ "\nconseq:\n" ^ (Cprinter.string_of_struc_formula conseq)) pos; *)
  (*         let rs1, prf1 = inner_entailer_octx c1 conseq  in *)
  (*         let rs2, prf2 = inner_entailer_octx c2 conseq  in *)
  (*         ((or_list_context rs1 rs2),(mkOrStrucLeft ctx conseq [prf1;prf2])) *)
  (*   | Ctx es -> begin *)
  (*       (\*let es = {es with es_formula = prune_preds prog es.es_formula } in*\) *)
  (*       let tmp, prf = inner_entailer 0 ctx conseq in *)
  (*       (filter_set tmp, prf) *)
  (*     end in *)

  let rec helper_inner (ctx11 : context) (f:ext_formula) : list_context * proof = 
    begin
      match f with
        | ECase b   -> 
	          (*let _ = print_string ("\nstart case:"^(Cprinter.string_of_ext_formula f)^"\n") in*)
              (* print_endline ("XXX helper of inner entailer"^Cprinter.string_of_prior_steps (CF.get_prior_steps ctx)); *)
              let ctx = add_to_context_num 1 ctx11 "case rule" in
	          if (List.length b.formula_case_exists)>0 then 
	            let ws = CP.fresh_spec_vars b.formula_case_exists in
	            let st = List.combine b.formula_case_exists ws in
	            let new_struc = subst_struc st [(ECase {b with formula_case_exists = []})]in
	            let new_ctx = push_exists_context ws ctx in
	            let nc,np = inner_entailer 1 new_ctx new_struc in 
	            (nc,(mkEexStep ctx [f] np))
	          else if (List.length b.formula_case_branches )=0 then ((SuccCtx [ctx]),TrueConseq)
	          else 
	            let rec helper l = match l with
	              | [] -> None
	              | (p,e)::t -> 
		                let tt = (syn_imply ctx p) in
		                (*print_string ("\n -------------:\n"^(Cprinter.string_of_context ctx)^"\n\n"^
		                  (Cprinter.string_of_pure_formula p)^"\n\n"^(string_of_bool tt)^"\n") ;*)
		                if tt then Some (p,e) else helper t  in
	            let r = helper b.formula_case_branches in
	            let r = match r with
	              | None -> begin
		              List.map (fun (c1,c2)-> 
			              let n_ctx = combine_context_and_unsat_now prog (ctx) (MCP.memoise_add_pure_N (MCP.mkMTrue pos) c1) in 
                          (*this unsat check is essential for completeness of result*)
				          if (isAnyFalseCtx n_ctx) then (SuccCtx[n_ctx],UnsatAnte)
				          else 
                            let n_ctx = prune_ctx prog n_ctx in
                            let n_ctx = normalize_frac_ctx prog n_ctx in
                            inner_entailer 2 n_ctx c2 ) b.formula_case_branches 
		            end
	              | Some (p,e) -> begin [inner_entailer 3 ctx e]end in
	            let rez1,rez2 = List.split r in
                let rez1 = List.fold_left (fun a c-> or_list_context (*list_context_union*) a c) (List.hd rez1) (List.tl rez1) in
	            (rez1,(mkCaseStep ctx [f] rez2))
        | EBase ({
		      formula_ext_explicit_inst =expl_inst;
		      formula_ext_implicit_inst = impl_inst;
		      formula_ext_exists = base_exists;
		      formula_ext_base = formula_base;
		      formula_ext_continuation = formula_cont;
		      formula_ext_pos = struc_pos;
	      } as b)  -> 
          if (List.length base_exists)>0 then 
	        let ws = CP.fresh_spec_vars base_exists in
	        let st = List.combine base_exists ws in
	        let new_struc = subst_struc st [(EBase {b with formula_ext_exists = []})]in
	        let new_ctx = push_exists_context ws ctx11 in
	        let nc,np = inner_entailer 4 new_ctx new_struc in 
	        (nc,(mkEexStep ctx11 [f] np))
	      else 
            (* XXXX explore the option to unfold the LHS *)
            
	        let n_ctx = (push_expl_impl_context expl_inst impl_inst ctx11 ) in
	        let n_ctx_list, prf = heap_entail_one_context prog (if (List.length formula_cont)>0 then true else is_folding)   n_ctx formula_base pos in
	        (*let _ = print_string ("pp: "^(Cprinter.string_of_spec_var_list b.formula_ext_explicit_inst)^"\n"^
	          (Cprinter.string_of_spec_var_list b.formula_ext_implicit_inst)^"\n"^
	          (Cprinter.string_of_context n_ctx)^"\n conseq: "^
	          (Cprinter.string_of_ext_formula f)^"\n"
	          ) in*)
	        (*let n_ctx_list = List.filter  (fun c -> not (isFalseCtx c)) n_ctx_list in*)
	        let n_ctx_list = pop_expl_impl_context expl_inst impl_inst n_ctx_list in
	        (*let _= print_string ("\n wrrap inst: "^(string_of_int (List.length formula_cont))^"\n"^
	          (Cprinter.string_of_spec_var_list (expl_inst@impl_inst))^"\n") in*)
	        (match n_ctx_list with
	          | FailCtx _ -> (n_ctx_list, prf)
	          | SuccCtx sc ->
		            if (List.length formula_cont)>0 then
                      let res, n_rpf = heap_entail_struc prog is_folding has_post n_ctx_list formula_cont pos pid in
                      (* let res, n_rpf = List.split (List.map (fun c->inner_entailer 5 c formula_cont) sc) in *)
                      (* let res = fold_context_left res in *)
                      let res = if !wrap_exists_implicit_explicit then  
		                push_exists_list_context (expl_inst@impl_inst) res 
		              else res in
		              (res, n_rpf) (* (mkBaseStep ctx11 [f] prf (mkCaseStep ctx11 [f] n_rpf)) *)
		            else	 
                      let res = if !wrap_exists_implicit_explicit then  
		                push_exists_list_context (expl_inst@impl_inst) n_ctx_list 
		              else n_ctx_list in
		              (*let _ = print_string ("\nresidue: "^(Cprinter.string_of_context_list res)^"\n  "^(string_of_bool (isFalseCtx (List.hd res)))^"\n") in*)
		              (res,prf)
            )
        | EAssume (ref_vars, post,(i,y)) -> if not has_post then report_error pos ("malfunction: this formula "^y^" can not have a post condition!")
	      else
	        let rs = clear_entailment_history ctx11 in
	        (*let _ =print_string ("before post:"^(Cprinter.string_of_context rs)^"\n") in*)
            (* TOCHECK : why compose_context fail to set unsat_flag? *)
	        let rs1 = CF.compose_context_formula rs post ref_vars Flow_replace pos in
	        (*let _ =print_string ("\n after post:"^(Cprinter.string_of_context rs1)^"\n") in*)
	        let rs2 = CF.transform_context (elim_unsat_es_now prog (ref 1)) rs1 in
            (*let _ =print_string ("\n after post and unsat:"^(Cprinter.string_of_context rs2)^"\n") in*)
	        let rs3 = add_path_id rs2 (pid,i) in
            let rs4 = prune_ctx prog rs3 in
            let rs4  = normalize_frac_ctx prog rs4 in
	        (*let _ = print_string (
	          "\n rs1:"^
	          (Cprinter.string_of_context rs1)
	          ^"\n rs2:"^
	          (Cprinter.string_of_context rs2)^"\n"
	          ) in*)
	        ((SuccCtx [rs4]),TrueConseq)
	    | EVariance e ->
		    (*let _ = print_string ("\ninner_entailer: EVariance: LHS: "^(Cprinter.string_of_context ctx)^"\n");
			        print_string ("\ninner_entailer: EVariance: RHS: "^(Cprinter.string_of_ext_formula f)^"\n")
			in*) 
			
			let es = match ctx11 with
			  | Ctx c -> c
			  | OCtx _ -> report_error no_pos ("inner_entailer: OCtx encountered \n"^(Cprinter.string_of_context ctx11))
            in
			
            (*
			let _ = print_string (List.fold_left (fun rs (v1,v2,mn) -> rs ^ " (" ^ (Cprinter.string_of_spec_var v1) ^ "," ^ (Cprinter.string_of_spec_var v2) ^ "@" ^ mn ^ ")") "innner_entailer: var_subst@EVariance: " es.CF.es_var_subst) in
			let string_ctx_lhs = Cprinter.string_of_pure_formula es.es_var_ctx_lhs in
			let str_var_subst  = List.map (fun (v1,v2,mn) -> ((Cprinter.string_of_spec_var v1), (Cprinter.string_of_spec_var v2))) es.CF.es_var_subst in
			*)
			let f = List.map (fun (v,_,_) -> v) es.CF.es_var_subst in
			(*let t = List.map (fun (_,v,_) -> CP.to_unprimed v) es.CF.es_var_subst in*)
			let t = List.map (fun (_,v,mn) -> let CP.SpecVar (t,i,p) = v in
							                  let nid = i^"_"^mn in
											  (*let _ = print_string ("New ident: " ^ nid ^ "\n") in*)
											  CP.to_unprimed (CP.SpecVar (t, nid, p))) es.CF.es_var_subst in

			let normalize_ctx_rhs =
			  let rec filter pformula =
				match pformula with
				  | CP.And (f1, f2, pos) -> let nf2 = CP.subst_avoid_capture f t f2 in
											let nf1 = filter f1 in
											if (CP.equalFormula f2 nf2) then nf1
											else CP.mkAnd nf1 nf2 pos
				  | _ -> let nf = CP.subst_avoid_capture f t pformula in
						   if (CP.equalFormula_f CP.eq_spec_var pformula nf) then CP.mkTrue no_pos
						   else nf
		      in filter es.es_var_ctx_rhs
			in 

			let nes = {es with CF.es_var_ctx_rhs = normalize_ctx_rhs} in
			(*
			let _ = print_string ("\ninner_entailer: ctx_lhs@EVariance: " ^ string_ctx_lhs ^ "\n") in
			let _ = print_string ("\ninner_entailer: ctx_rhs@EVariance: " ^ (Cprinter.string_of_pure_formula filtered_ctx_rhs) ^ "\n") in

			let _ = print_string ("\ninner_entailer: call graph adding: " ^ string_ctx_lhs ^ " ->" ^ (Cprinter.string_of_pure_formula filtered_ctx_rhs) ^ "\n") in
            *)

			variance_graph := !variance_graph @ [(es.es_var_ctx_lhs, normalize_ctx_rhs)];
			var_checked_list := !var_checked_list @ [(nes,e)];
		    inner_entailer 7 ctx11 e.Cformula.formula_var_continuation
    end (* helper_inner match *)
        (* in *)
        (*let _ = print_string ("\n inner entailer: "^(string_of_int (List.length conseq))^"\n") in
	      let _ = print_string ("\n thre conseq : "^(if ((List.length conseq)==3) then (Cprinter.string_of_struc_formula conseq) else "")^"\n") in*)

  and inner_entailer i (ctx22 : context) (conseq : struc_formula): list_context * proof = 
    let _ = match ctx22 with 
      | OCtx _ ->
            Error.report_warning {
                Error.error_loc = !post_pos;
                Error.error_text = ("[inner entailer"^(string_of_int i)^"] unexpected dealing with OCtx "^(string_of_int (count_octx ctx22))^"\n"^
                    (Cprinter.string_of_context_short ctx22))
            }
      | _ -> () in
    if (List.length conseq)>0 then	
      (* this call captures an OCtx, why?? *)
	  let ctx = CF.add_to_context_num 2 ctx22 "para OR on conseq" in
	  let r = List.map (helper_inner ctx) conseq in
	  let l1,l2 = List.split r in
	  ((fold_context_left l1),(mkCaseStep ctx conseq l2))
    else 
      (* TODO : can do a stronger falsity check on LHS *)
	  (CF.mkFailCtx_in(Trivial_Reason "struc conseq is [] meaning false") , UnsatConseq)
          (* ((SuccCtx [ctx]),TrueConseq) *)
  in
  let adv_u = advance_unfold_struc prog ctx_00 conseq in
  if adv_u==[] then
      inner_entailer 8 ctx_00 conseq 
  else
      (* inner_entailer 8 ctx_00 conseq  *)
    let a = snd (List.hd adv_u) in
      process_unfold prog estate conseq a is_folding pos has_post pid

and heap_entail_variance
      (prog : prog_decl) 
      (es : entail_state) 
      (e : ext_variance_formula) =
  let loc = e.formula_var_pos in

  let string_of_es_var_measure el = "[" ^ (List.fold_left (fun rs e -> let str = Cprinter.string_of_formula_exp e in
																if rs = "" then str else rs ^ ", " ^ str) "" el) ^ "]" in

  Debug.print_info "termination" ("Transition from state " ^ (Cprinter.string_of_pure_formula es.es_var_ctx_lhs) ^ " to state " ^ (Cprinter.string_of_pure_formula es.es_var_ctx_rhs)) loc;

  let var_label_rhs = match e.formula_var_label with
	| None -> report_error no_pos ("termination: error with auto-numbering variance label - the variance does not have a label \n")
	| Some i -> i
  in

  let var_label_lhs = match es.es_var_label with
	| None -> report_error no_pos ("termination: error with auto-numbering variance label - the variance does not have a label \n")
	| Some i -> i
  in
  
  if (var_label_lhs = var_label_rhs && var_label_rhs > 0) then
	let lhs_measures = es.es_var_measures in
	let rhs_measures = e.formula_var_measures in
	let rec binding lhs_m rhs_m =
	  if ((List.length lhs_m) != (List.length rhs_m)) then
		report_error no_pos ("termination: variance checking: LHS does not match RHS \n")
	  else match lhs_m with
		| [] -> []
		| h::t -> (h, (List.hd rhs_m))::(binding t (List.tl rhs_m)) in
	let binding_measures = binding lhs_measures rhs_measures in
	let fun_check_term lst_measures = (* [(m1,n1),(m2,n2)] -> m1=n1 & m1>=lb1 & m2>n2 & m2>=lb2*) 
	  let term_formula = 
		List.fold_right (fun (l,r) (flag,res) ->
		  let lower_bound = match (snd r) with
		    | None -> report_error no_pos ("termination: variance checking: error with lower bound in termination checking \n")
		    | Some exp -> exp in
		  let boundedness_checking_formula = CP.BForm (CP.mkGte l lower_bound loc, None) in
		  let lexico_ranking_formula = 
		    if flag then CP.BForm (CP.mkGt (CP.mkSubtract l (fst r) loc) (CP.mkIConst 0 loc) loc, None)
			else CP.BForm (CP.mkEq l (fst r) loc, None) in
		  let f = CP.mkAnd lexico_ranking_formula boundedness_checking_formula loc in  
		  (false, CP.mkAnd f res loc)) lst_measures (true, CP.mkTrue loc)
	  in
      (*let _ = print_string ("\ntermination: term checking formula: "^(Cprinter.string_of_struc_formula [mkEBase (snd term_formula) loc])) in*)
	  (heap_entail_conjunct_lhs_struc prog false false (CF.Ctx es) [mkEBase (snd term_formula) loc] no_pos None)  
	in
	let lexico_measures = (* [(m1,n1),(m2,n2)] -> [[(m1,n1)],[(m1,n1),(m2,n2)]] *)
	  List.fold_right (fun bm res -> [bm]::(List.map (fun e -> bm::e) res)) binding_measures []	
	in
	let lst_res = List.map (fun lm -> fun_check_term lm) lexico_measures in
	if (List.exists (fun (rs,prf) -> let _ = Prooftracer.log_proof prf in not (CF.isFailCtx rs)) lst_res) then
	  Debug.print_info "termination" ("checking termination by variance " ^ (string_of_es_var_measure es.es_var_measures) ^ " : ok") loc
	else
	  Debug.print_info "termination" ("checking termination by variance " ^ (string_of_es_var_measure es.es_var_measures) ^ " : failed") loc;
  else if (var_label_lhs = var_label_rhs && var_label_rhs = 0) then
	Debug.print_info "termination" ("terminating state") loc
  else if (var_label_lhs = var_label_rhs && var_label_rhs = -1) then
	Debug.print_info "termination" ("non-terminating state") loc
  else if (var_label_lhs > var_label_rhs) then
	(* Already checked UNSAT(D) at heap_entail_one_context_struc *)
	Debug.print_info "termination" ("transition from variance " ^ (string_of_int var_label_lhs) ^ " to " ^ (string_of_int var_label_rhs) ^ " : safe") loc  		
  else
	Debug.print_info "termination" ("transition from variance " ^ (string_of_int var_label_lhs) ^ " to " ^ (string_of_int var_label_rhs) ^ " : invalid") loc

and heap_entail_init (prog : prog_decl) (is_folding : bool)  (cl : list_context) (conseq : formula) pos : (list_context * proof) =
  match cl with
    | FailCtx fr -> (cl,Failure)
    | SuccCtx _ ->
	      reset_formula_point_id();
	      let conseq = rename_labels_formula conseq in
	      let rename_es es = {es with es_formula = rename_labels_formula_ante es.es_formula}in
	      let rec prepare_es es = {es with 
			  es_success_pts  = ([]: (formula_label * formula_label)  list)  ;(* successful pt from conseq *)
			  es_residue_pts  = residue_labels_in_formula es.es_formula   ;(* residue pts from antecedent *)
			  es_id      = (fst (fresh_formula_label ""))              ; (* unique +ve id *)
			  es_orig_ante   = es.es_formula;
			  es_orig_conseq = struc_formula_of_formula conseq pos;} in	
	      let cl_new = transform_list_context ((fun es-> Ctx(prepare_es(rename_es (reset_original_es es)))),(fun c->c)) cl in
	      let conseq_new = conseq in
	      heap_entail prog is_folding  cl_new conseq_new pos

and heap_entail_debug
      p is_folding  cl conseq 
      pos : (list_context * proof) = 
  Gen.Debug.no_2 "heap_entail---------\n\n"
      (Cprinter.string_of_list_context)
      (Cprinter.string_of_formula)
      (fun _ -> "?")
      (fun cl conseq -> heap_entail p is_folding  cl conseq pos) cl conseq

and heap_entail (prog : prog_decl) (is_folding : bool)  (cl : list_context) (conseq : formula) pos : (list_context * proof) =
  match cl with 
    | FailCtx _ -> (cl,Failure)
    | SuccCtx cl ->
	      if !Globals.use_set || Gen.is_empty cl then
            let tmp1 = List.map (fun c -> heap_entail_one_context prog is_folding  c conseq pos) cl in
            let tmp2, tmp_prfs = List.split tmp1 in
            let prf = mkContextList cl (Cformula.formula_to_struc_formula conseq) tmp_prfs in
            ((fold_context_left tmp2), prf)
	      else
            (heap_entail_one_context prog is_folding  (List.hd cl) conseq pos)

and heap_entail_one_context prog is_folding  ctx conseq pos =
  Gen.Debug.loop_2_no "heap_entail_one_context" (Cprinter.string_of_context) (Cprinter.string_of_formula) (fun (l,p) -> Cprinter.string_of_list_context l) 
      (fun ctx conseq -> heap_entail_one_context_a prog is_folding  ctx conseq pos) ctx conseq

(*   and heap_entail_one_context prog is_folding  ctx conseq pos =  *)
(* heap_entail_one_context_a prog is_folding  ctx conseq pos *)

and heap_entail_one_context_a (prog : prog_decl) (is_folding : bool)  (ctx : context) (conseq : formula) pos : (list_context * proof) =
  Debug.devel_pprint ("heap_entail_one_context:"
  ^ "\nctx:\n" ^ (Cprinter.string_of_context ctx)
  ^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq)^"\n") pos;
    if isAnyFalseCtx ctx then
      (* check this first so that false => false is true (with false residual) *)
      (SuccCtx [ctx], UnsatAnte)
    else if isStrictConstTrue conseq then
      (SuccCtx [ctx], TrueConseq)
    else if isAnyFalseCtx ctx then
      (SuccCtx [ctx], UnsatAnte)
    else
      heap_entail_after_sat prog is_folding  ctx conseq pos ([])


and heap_entail_after_sat prog is_folding  (ctx:CF.context) (conseq:CF.formula) pos
      (ss:CF.steps) : (list_context * proof) = 
  match ctx with
    | OCtx (c1, c2) ->
          Debug.devel_pprint ("heap_entail_after_sat:"
		  ^ "\nctx:\n" ^ (Cprinter.string_of_context ctx)
		  ^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq)) pos;
          let rs1, prf1 = heap_entail_after_sat prog is_folding
            c1 conseq pos (CF.add_to_steps ss "left OR 1 on ante") in  
          let rs2, prf2 = heap_entail_after_sat prog is_folding
            c2 conseq pos (CF.add_to_steps ss "right OR 1 on ante") in
	      (*let _ = print_string("\nheap_entail_after_sat fail o1: " ^(string_of_bool (isFailCtx rs1))) in
	        let _ = print_string("\nheap_entail_after_sat fail o2: " ^(string_of_bool (isFailCtx rs2))) in
	        let _ = print_string("\nheap_entail_after_sat fail r: " ^(string_of_bool (isFailCtx (or_list_context_inner rs1 rs2)))) in
	        let _ = if  (isFailCtx rs1) then print_string ("\npre: "^(Cprinter.string_of_context c1) ^"\n post: \n"^(Cprinter.string_of_formula conseq)^"\n") else () in
	        let _ = if  (isFailCtx rs2) then print_string ("\npre: "^(Cprinter.string_of_context c2) ^"\n post: \n"^(Cprinter.string_of_formula conseq)^"\n") else () in
	      *)
	      ((or_list_context rs1 rs2),(mkOrLeft ctx conseq [prf1;prf2]))
    | Ctx es -> begin
        Debug.devel_pprint ("heap_entail_after_sat: invoking heap_entail_conjunct_lhs"
		^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx)
		^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq)) pos;
        (* print_string ("going: "^(Cprinter.string_of_formula es.es_formula)^"\n") ;*)
        (*let es = {es with es_formula = prune_preds prog es.es_formula} in
          let conseq = prune_preds prog conseq in*)
        let es = (CF.add_to_estate_with_steps es ss) in
        let tmp, prf = heap_entail_conjunct_lhs prog is_folding  (Ctx es) conseq pos in  
	    (filter_set tmp, prf)
      end

(*
  and heap_entail_conjunct_lhs prog is_folding  (ctx:context) conseq pos : (list_context * proof) 
  = Gen.Debug.no_1 "heap_entail_conjunct_lhs" Cprinter.string_of_context (fun _ -> "?") 
  (fun ctx -> heap_entail_conjunct_lhs_x  prog is_folding  ctx conseq pos) ctx 
*)

and heap_entail_conjunct_lhs p  = heap_entail_conjunct_lhs_x p

(* check entailment when lhs is normal-form, rhs is a conjunct *)
and heap_entail_conjunct_lhs_x prog is_folding  (ctx:context) (conseq:CF.formula) pos : (list_context * proof) =
  (* pre ; LHS is not an OCtx *)
  match conseq with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos1}) ->
          Debug.devel_pprint ("heap_entail_conjunct_lhs: \nante:\n"
		  ^ (Cprinter.string_of_context ctx)
		  ^ "\nconseq:\n"
		  ^ (Cprinter.string_of_formula conseq)) pos;
          let ctx_L = CF.add_to_context_num 3 ctx "left OR 2 on conseq" in
          let ctx_R = CF.add_to_context_num 4 ctx "right OR 2 on conseq" in
          if !Globals.use_set then
	        let rs1, prf1 = heap_entail_conjunct_lhs_x prog is_folding  ctx_L f1 pos in
	        let rs2, prf2 = heap_entail_conjunct_lhs_x prog is_folding  ctx_R f2 pos in
	        ((fold_context_left [rs1;rs2]),( mkOrRight ctx conseq [prf1; prf2]))		  
          else
	        let rs1, prf1 = heap_entail_conjunct_lhs_x prog is_folding  ctx_L f1 pos in
	        if (isFailCtx rs1) then
	          let rs2, prf2 = heap_entail_conjunct_lhs_x prog is_folding  ctx_R f2 pos in
	          (filter_set rs2, prf2)
	        else
	          (filter_set rs1, prf1)
    | _ -> begin
        let r1,p1 =
	      if !Globals.allow_imm (*(contains_immutable_ctx ctx) or (contains_immutable conseq)*) then
            begin
              Debug.devel_pprint ("heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases") pos;
	          heap_entail_split_rhs_phases prog is_folding  ctx conseq false pos     
            end
	      else
	        heap_entail_conjunct prog is_folding  ctx conseq pos     
        in
	    (r1,p1)
      end

(* 23.10.2008 *)
(* for empty RHS heap:
   - move the explicit instantiations from the RHS to the LHS
   - remove the explicit instantiated vars from the existential vars of the conseq
   - add the existential vars from the conseq to the existential vars from the antecedent
   - f represents the consequent
*)
(* and move_lemma_expl_inst_ctx_list_x (ctx : list_context) (f : MCP.mix_formula) : list_context = *)
(*   let fct es =  *)
(*     let f = MCP.find_rel_constraints f es.es_expl_vars in *)
(*     let new_es = (pop_exists_estate es.es_expl_vars es) in *)
(*     let nf =  *)
(*       let f2 = if (new_es.es_evars = []) then f else (elim_exists_mix_formula(\*_debug*\) new_es.es_evars f no_pos) in *)
(*       CF.mkStar new_es.es_formula (formula_of_mix_formula f2 no_pos) Flow_combine no_pos in *)
(*     Ctx {new_es with *)
(*           es_gen_impl_vars = []; *)
(* 	        es_ante_evars = new_es.es_ante_evars @ new_es.es_evars; *)
(* 	        es_formula = nf; *)
(* 	        es_unsat_flag = false; } in *)
(*     transform_list_context (fct,(fun c->c)) ctx *)

(* and move_lemma_expl_inst_ctx_list (ctx:list_context)(f:MCP.mix_formula):list_context = *)
(*         let pr1 = Cprinter.string_of_list_context in *)
(*         let pr2 = Cprinter.string_of_mix_formula in *)
(*   Gen.Debug.no_2 "move_lemma_expl_inst_ctx_list" pr1 pr2 pr1  *)
(*       move_lemma_expl_inst_ctx_list_x ctx f *)


and move_expl_inst_ctx_list (ctx:list_context)(f:MCP.mix_formula) fp:list_context =
  let pr1 = Cprinter.string_of_list_context in
  let pr2 = Cprinter.string_of_mix_formula in
  let pr3 = Cprinter.string_of_perm_formula in
  Gen.Debug.no_3 "move_expl_inst_ctx_list" pr1 pr2 pr3 pr1 
      (fun c1 c2 _->move_expl_inst_ctx_list_x ctx f fp) ctx f fp

and move_expl_inst_ctx_list_x (ctx:list_context)(f:MCP.mix_formula) (fp:Cperm.perm_formula):list_context = 
  let fct es = 
    let f = MCP.find_rel_constraints f (es.es_gen_expl_vars@es.es_gen_impl_vars) in
	let pr = Cperm.find_rel_constraints fp (es.es_gen_expl_vars@es.es_gen_impl_vars) in
    let nf = 
      let f2,f2pr = if (es.es_evars = []) then f,pr else (elim_exists_mix_formula(*_debug*) es.es_evars f no_pos),(Cperm.elim_pr_exists1 es.es_evars pr) in
      CF.mkStar es.es_formula (formula_of_mix_formula f2 f2pr no_pos) Flow_combine no_pos in
    (*let f1 = formula_of_memo_pure (MCP.memo_pure_push_exists (es.es_gen_impl_vars@es.es_evars) f ) no_pos in*)
    Ctx {es with
	    es_gen_impl_vars = [];
	    es_ante_evars = es.es_ante_evars @ es.es_evars;
	    es_formula = nf;
	    es_unsat_flag = false; } in
  transform_list_context (fct,(fun c->c)) ctx

(* from a list containing equaltions of the form vi = wi -> obtain two lists [vi]  and [wi] *)
and obtain_subst l =
  match l with
    | CP.BForm(CP.Eq(CP.Var(e1, _), CP.Var(e2, _), _),_)::r -> ((e1::(fst (obtain_subst r))), (e2::(snd (obtain_subst r))))
    | _::r -> ((fst (obtain_subst r)), (snd (obtain_subst r)))
    | [] -> ([],[])

and coer_target prog (coer : coercion_decl) (node:CF.h_formula) (target_rhs : CF.formula) (lhs : CF.formula) : bool =
  Gen.Debug.no_3 "coer_target" (* Cprinter.string_of_coercion  *)
      Cprinter.string_of_h_formula Cprinter.string_of_formula Cprinter.string_of_formula string_of_bool 
      (fun _ _ _ -> coer_target_a prog coer node target_rhs lhs) node lhs target_rhs

(* check whether the target of a coercion is in the RHS of the entailment *)
(* coer: the coercion lemma to be applied *)
(* node: the node to which the coercion applies *)
(* lhs and rhs - the antecedent and consequent, respectively *)
and coer_target_a prog (coer : coercion_decl) (node:CF.h_formula) (target_rhs : CF.formula) (lhs : CF.formula) : bool =
  let coer_lhs = coer.coercion_head in
  let coer_rhs = coer.coercion_body in
  let coer_lhs_heap, coer_lhs_guard,coer_lhs_flow, _, coer_lhs_branches, _ = split_components coer_lhs in
  let rhs_heap, rhs_pure, rhs_flow, _, rhs_branches, _ = split_components target_rhs in
  let lhs_heap, lhs_pure, lhs_flow, _, lhs_branches, _ = split_components lhs in
  (*let _ = print_string("coer_lhs_heap = " ^ (Cprinter.string_of_h_formula coer_lhs_heap) ^ "\n") in
    let _ = print_string("node = " ^ (Cprinter.string_of_h_formula node) ^ "\n") in*)
  (* node - the node to which we want to apply the coercion rule *)
  (* need to find the substitution *)
  match node, coer_lhs_heap with
    | ViewNode ({ h_formula_view_node = p1;
	  h_formula_view_name = c1;
	  h_formula_view_origins = origs;
	  h_formula_view_arguments = ps1}),
	  ViewNode ({h_formula_view_node = p2;
	  h_formula_view_name = c2;
	  h_formula_view_arguments = ps2}) when c1=c2 ->
	      begin
	        (* apply the substitution *)
	        let coer_rhs_new = subst_avoid_capture (p2 :: ps2) (p1 :: ps1) coer_rhs in
	        let coer_lhs_new = subst_avoid_capture (p2 :: ps2) (p1 :: ps1) coer_lhs in
	        (*let _ = print_string("coer_rhs = " ^ (Cprinter.string_of_formula coer_rhs) ^ "\n") in*)
	        (*let _ = print_string("coer_rhs_new = " ^ (Cprinter.string_of_formula coer_rhs_new) ^ "\n") in *)
	        (* find the targets from the RHS of the coercion *)
	        let top_level_vars = (CF.f_top_level_vars coer_rhs_new) in
	        let target = (List.filter (fun x -> List.mem x top_level_vars) (CF.fv coer_rhs_new)) in
	        let target = (List.filter (fun x -> (List.mem x (CF.fv coer_lhs_new))) target) in
	        (*let _ = print_string ("Target:" ^ (Cprinter.string_of_spec_var_list target) ^ "\n") in*)
	        let coer_rhs_h, _,_, _, _, _ = split_components coer_rhs_new in
	        (* check for each target if it appears in the consequent *)
	        let all_targets = (List.map (fun x -> (check_one_target prog node x lhs_pure rhs_pure rhs_heap coer_rhs_h)) target) in
            List.exists(fun c->c) all_targets
	      end
    | _ -> Error.report_error {Error.error_loc = no_pos; Error.error_text = "malfunction coer_target recieved non views"}
	      (* given a spec var -> return the entire node *)
and get_node (sv : CP.spec_var) (f : CF.h_formula) : CF.h_formula =
  match f with
    | Star({ h_formula_star_h1 = f1; h_formula_star_h2 = f2}) ->
	      let res1 = (get_node sv f1) in
	      begin
	        match res1 with
	          | HFalse -> (get_node sv f2)
	          | _ -> res1
	      end
    | DataNode({h_formula_data_node = sv1; h_formula_data_name = name}) ->
	      if (CP.eq_spec_var sv sv1)
	      then f
	      else HFalse
    | ViewNode({h_formula_view_node = sv1; h_formula_view_name = name}) ->
	      if (CP.eq_spec_var sv sv1)
	      then f
	      else HFalse
    | _ -> HFalse

and check_one_target prog node (target : CP.spec_var) (lhs_pure : MCP.mix_formula) (target_rhs_p : MCP.mix_formula) (target_rhs_h : CF.h_formula) (coer_rhs_h : CF.h_formula)
      : bool =
  let pr1 = Cprinter.string_of_spec_var in
  let pr2 = Cprinter.string_of_mix_formula in
  let pr3 = Cprinter.string_of_h_formula in
  Gen.Debug.no_3 "check_one_target" pr1 pr2 pr3 string_of_bool
      (fun _ _ _ -> check_one_target_x prog node (target : CP.spec_var) (lhs_pure : MCP.mix_formula) (target_rhs_p : MCP.mix_formula) (target_rhs_h : CF.h_formula) (coer_rhs_h : CF.h_formula)) target target_rhs_p target_rhs_h 

(* check whether target appears in rhs *)
(* we need lhs_pure to compute the alias set of target *)
and check_one_target_x prog node (target : CP.spec_var) (lhs_pure : MCP.mix_formula) (target_rhs_p : MCP.mix_formula) (target_rhs_h : CF.h_formula) (coer_rhs_h : CF.h_formula)
      : bool =
  (*let _ = print_string("check_one_target: target: " ^ (Cprinter.string_of_spec_var target) ^ "\n") in*)
  let lhs_eqns = MCP.ptr_equations_with_null lhs_pure in
  let rhs_eqns = MCP.ptr_equations_with_null target_rhs_p in
  let lhs_asets = MCP.alias_nth 7 (lhs_eqns@rhs_eqns) in
  let lhs_targetasets1 = MCP.get_aset lhs_asets target in
  let lhs_targetasets =
    if CP.mem target lhs_targetasets1 then lhs_targetasets1
    else target :: lhs_targetasets1 in
  let n_l_v =  h_node_list target_rhs_h in
  let l = Gen.BList.intersect_eq CP.eq_spec_var lhs_targetasets n_l_v in
  (l!=[])     

and check_one_target_old prog node (target : CP.spec_var) (lhs_pure : MCP.mix_formula) (target_rhs_p : MCP.mix_formula) (target_rhs_h : CF.h_formula) (coer_rhs_h : CF.h_formula)
      : bool =
  (*let _ = print_string("check_one_target: target: " ^ (Cprinter.string_of_spec_var target) ^ "\n") in*)
  let lhs_eqns = MCP.ptr_equations_with_null lhs_pure in
  let lhs_asets = MCP.alias_nth 8 lhs_eqns in
  let lhs_targetasets1 = MCP.get_aset lhs_asets target in
  let lhs_targetasets =
    if CP.mem target lhs_targetasets1 then lhs_targetasets1
    else target :: lhs_targetasets1 in
  let fnode_results = (Context.deprecated_find_node prog node target_rhs_h target_rhs_p lhs_targetasets no_pos) in
  begin
    match fnode_results with
	  | Context.Deprecated_Failed -> (*let _ = print_string("[check_one_target]: failed\n") in*) false
	  | Context.Deprecated_NoMatch -> (*let _ = print_string("[check_one_target]: no match\n") in*) false
	  | Context.Deprecated_Match (matches) ->
	        begin
	          match matches with
		        | x :: rest -> 
		              begin
                        let anode = x.Context.match_res_lhs_node in
		                (* update the current phase *)
			            (* crt_phase := phase; *)
		                let target_node = get_node target coer_rhs_h in
		                let _ = Debug.devel_pprint ("Target: " ^ (Cprinter.string_of_h_formula target_node) ^ "\n") no_pos in
		                let _ = Debug.devel_pprint ("Target match: " ^ (Cprinter.string_of_h_formula anode) ^ "\n") no_pos in
			            begin
			              match target_node, anode with
			                | ViewNode ({h_formula_view_node = p1; h_formula_view_name = c1}),
			                  ViewNode ({h_formula_view_node = p2; h_formula_view_name = c2}) when c1=c2 ->(true)
			                | DataNode ({h_formula_data_node = p1; h_formula_data_name = c1}),
				                  DataNode ({h_formula_data_node = p2; h_formula_data_name = c2}) when c1=c2 ->(true)
			                | _ ->	false
			            end
		              end
		        | [] -> false
	        end
  end

(* checks whether a coercion is distributive *)
and is_distributive	(coer : coercion_decl) : bool =
  let coer_lhs = coer.coercion_head in
  let coer_rhs = coer.coercion_body in
  let coer_lhs_heap, _,_, _, _, _ = split_components coer_lhs in
  let coer_rhs_heap, _,_, _, _, _ = split_components coer_rhs in
  let top_level_lhs = top_level_vars coer_lhs_heap in
  let top_level_rhs = top_level_vars coer_rhs_heap in
  not(List.mem false (List.map (fun x -> check_one_node x top_level_rhs coer_lhs_heap coer_rhs_heap) top_level_lhs))

(*  checks whether sv is present on the lhs and points to the same view *)
and check_one_node (sv : CP.spec_var) (top_level_rhs : CP.spec_var list) (lhs_heap : CF.h_formula) (rhs_heap : CF.h_formula) : bool =
  match top_level_rhs with
    | h :: r ->
	      if (CP.eq_spec_var h sv) && (String.compare (CF.get_node_name (get_node sv lhs_heap)) (CF.get_node_name (get_node h rhs_heap))) == 0 then
	        true
	      else (check_one_node sv r lhs_heap rhs_heap)
    | [] -> false

(* returns the list of free vars from the rhs that do not appear in the lhs *)
and fv_rhs (lhs : CF.formula) (rhs : CF.formula) : CP.spec_var list =
  let lhs_fv = (CF.fv lhs) in
  let rhs_fv = (CF.fv rhs) in
  (List.filter (fun x -> not(List.mem x lhs_fv)) rhs_fv)

(*__________________*)

and split_phase_debug_lhs h = Gen.Debug.no_1 "split_phase(lhs)"
  Cprinter.string_of_h_formula 
  (fun (a,b,c) -> "RD = " ^ (Cprinter.string_of_h_formula a) ^ "; WR = " ^ (Cprinter.string_of_h_formula b) ^ "; NEXT = " ^ (Cprinter.string_of_h_formula c) ^ "\n") 
  split_phase h

and split_phase_debug_rhs h = Gen.Debug.no_1 "split_phase(rhs)"
  Cprinter.string_of_h_formula 
  (fun (a,b,c) -> "RD = " ^ (Cprinter.string_of_h_formula a) ^ "; WR = " ^ (Cprinter.string_of_h_formula b) ^ "; NEXT = " ^ (Cprinter.string_of_h_formula c) ^ "\n") 
  split_phase h

and split_phase (h : h_formula) : (h_formula * h_formula * h_formula )= 
  match h with
    | Phase ({h_formula_phase_rd = h1;
	  h_formula_phase_rw = h2;
	  h_formula_phase_pos = pos}) -> 
	      let h3, h4 = split_wr_phase h2 in
	      (h1, h3, h4)
    | Star _ ->
	      let h3, h4 = split_wr_phase h in
	      (HTrue, h3, h4)
    | _ ->
	      if (CF.contains_mutable_h_formula h) then
	        (HTrue, h, HTrue)
	      else
	        (h, HTrue, HTrue)

and split_wr_phase (h : h_formula) : (h_formula * h_formula) = 
  match h with 
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) -> 
	      (match h2 with
	        | Phase _ -> (h1, h2)
	        | Star ({h_formula_star_h1 = sh1;
		      h_formula_star_h2 = sh2;
		      h_formula_star_pos = spos}) ->
		          split_wr_phase (CF.mkStarH_nn (CF.mkStarH_nn h1 sh1 pos) sh2 pos)
	        | _ -> (h, HTrue))
    | Conj _ -> report_error no_pos ("[solver.ml] : Conjunction should not appear at this level \n")
    | Phase({h_formula_phase_rd = h1;
	  h_formula_phase_rw = h2;
	  h_formula_phase_pos = pos}) ->
	      (HTrue, h)
    | _ -> (h, HTrue)


and heap_entail_split_rhs_phases
      p is_folding  ctx0 conseq d
      pos : (list_context * proof) =
  Gen.Debug.no_2 "heap_entail_split_rhs_phases"
      (fun x -> Cprinter.string_of_context x)
      (Cprinter.string_of_formula)
      (fun (lc,_) -> Cprinter.string_of_list_context lc)
      (fun _ _ -> heap_entail_split_rhs_phases_x p is_folding  ctx0 conseq d pos) ctx0 conseq

and heap_entail_split_rhs_phases_x
      (prog : prog_decl) 
      (is_folding : bool) 
      (ctx_0 : context) 
      (conseq : formula) 
      (drop_read_phase : bool)
      pos : (list_context * proof) =
  let ctx_with_rhs =  (* ctx_0 in *)
	let (h, p, fl, pr, b, t) = CF.split_components conseq in
    let eqns = (MCP.ptr_equations_without_null p) in
    CF.set_context (fun es -> {es with es_rhs_eqset=es.es_rhs_eqset@eqns}) ctx_0 in
  let helper ctx_00 h p (* mix pure *) (func : CF.h_formula -> MCP.mix_formula -> CF.formula) = 
    (* let ctx_0 = (Cformula.transform_context *)
    (* 	(fun es -> *)
    (* 		Ctx{es with *)
    (* 			(\* reset the substitution list *\) *)
    (* 		    es_subst = ([], []); *)
    (* 		})) ctx_0 *)
    (* in *)

    let h1, h2, h3 = split_phase(*_debug_rhs*) h in
    if(is_true h1) && (is_true h2) && (is_true h3) then
      (* no heap on the RHS *)
      heap_entail_conjunct prog is_folding  ctx_00 conseq pos
    else

      if ((is_true h1) && (is_true h3))
	    or ((is_true h2) && (is_true h3))
      then
	    (* only one phase is not emp *)
	    heap_n_pure_entail prog is_folding  ctx_00 conseq (choose_not_true_heap h1 h2 h3) p func drop_read_phase pos
      else
	    if ((is_true h1) && (is_true h2)) then (* does split_phase allow this *)
	      let new_conseq = func h3 p in
	      if not(contains_phase h3) then
	        (* h3 is the only non empty phase and it does not contain any nested phases *)
	        heap_n_pure_entail prog is_folding  ctx_00 conseq (choose_not_true_heap h1 h2 h3) p func drop_read_phase pos
 	      else
	        heap_entail_split_rhs_phases_x prog is_folding  ctx_00 new_conseq (contains_mutable new_conseq) pos
	    else
	      let res_ctx, res_prf = 
	        (	    
	            (* entail the read phase heap *)
	            let (after_rd_ctx, after_rd_prf) = heap_entail_rhs_read_phase prog is_folding  ctx_00 h1 h2 h3 func pos in
	            (* entail the write phase heap *)
	            let after_wr_ctx, after_wr_prfs = heap_entail_rhs_write_phase prog is_folding  after_rd_ctx after_rd_prf conseq h1 h2 h3 func drop_read_phase pos in
	            (* entail the nested phase heap *)
	            heap_entail_rhs_nested_phase prog is_folding  after_wr_ctx after_wr_prfs conseq h1 h2 h3 func drop_read_phase pos
	        )
	      in 
	      (* entail the pure part *)
	      match res_ctx with
	        | SuccCtx (cl) ->
	              (* let _ = print_string("************************************************************************\n") in *)
	              (* let _ = print_string("[heap_n_pure_entail]: entail the pure part: p =" ^ (Cprinter.string_of_mix_formula p) ^ "\n") in *)
	              (* let _ = print_string("************************************************************************\n") in *)
	              let res = List.map (fun c -> 
		              let new_conseq, aux_conseq_from_fold = 
		                (match c with 
		                  | Ctx(estate) -> 
		                        subst_avoid_capture (fst estate.es_subst) (snd estate.es_subst) (func HTrue p), 
		                        subst_avoid_capture (fst estate.es_subst) (snd estate.es_subst) (func HTrue (MCP.mix_of_pure estate.es_aux_conseq))
		                  | OCtx _ -> report_error no_pos ("Disunctive context\n"))
		              in 
		              let new_conseq = CF.mkStar new_conseq aux_conseq_from_fold Flow_combine pos in
		              heap_entail_conjunct prog is_folding  c new_conseq pos) cl 
	              in
	              let res_ctx, res_prf = List.split res in
	              let res_prf = mkContextList cl (Cformula.struc_formula_of_formula conseq pos) res_prf in
	              let res_ctx = fold_context_left res_ctx in 
	              (res_ctx, res_prf)
	        | FailCtx _ -> (res_ctx, res_prf)	    
  in

  Debug.devel_pprint ("heap_entail_split_rhs_phases: 
                            \nante:\n"
  ^ (Cprinter.string_of_context ctx_0)
  ^ "\nconseq:\n"
  ^ (Cprinter.string_of_formula conseq)) pos;

  match ctx_0 with
    | Ctx estate -> begin
        let ante = estate.es_formula in
        match ante with
	      | Exists ({formula_exists_qvars = qvars;
		    formula_exists_heap = qh;
		    formula_exists_pure = qp;
			formula_exists_perm = qpr;
		    formula_exists_type = qt;
		    formula_exists_flow = qfl;
		    formula_exists_branches = qb;
		    formula_exists_pos = pos}) ->
	            (* ws are the newly generated fresh vars for the existentially quantified vars in the LHS *)
	            let ws = CP.fresh_spec_vars qvars in
	            (* new ctx is the new context after substituting the fresh vars for the exist quantified vars *)
	            let new_ctx = eliminate_exist_from_LHS qvars qh qp qt qfl qpr qb pos estate in
	            (* call the entailment procedure for the new context - with the existential vars substituted by fresh vars *)
	            let rs, prf1 =  heap_entail_split_rhs_phases prog is_folding  new_ctx conseq drop_read_phase pos in
	            let new_rs =
	              if !Globals.wrap_exist then
	                (* the fresh vars - that have been used to substitute the existenaltially quantified vars - need to be existentially quantified after the entailment *)
	                (add_exist_vars_to_ctx_list rs ws)
	              else
	                rs
	            in
	            (* log the transformation for the proof tracere *)
	            let prf = mkExLeft ctx_0 conseq qvars ws prf1 in
	            (new_rs, prf)
	      | _ -> begin
	          match conseq with  
	            | Base(bf) -> 
	                  let (h, p, fl, pr, b, t) = CF.split_components conseq in
	                  helper ctx_with_rhs (* ctx_0 *) h p (fun xh xp -> CF.mkBase xh xp t fl pr b pos)
	            | Exists ({formula_exists_qvars = qvars;
		          formula_exists_heap = qh;
		          formula_exists_pure = qp;
				  formula_exists_perm = qpr;
		          formula_exists_type = qt;
		          formula_exists_flow = qfl;
		          formula_exists_branches = qb;
		          formula_exists_pos = pos}) ->
	                  (* quantifiers on the RHS. Keep them for later processing *)
	                  let ws = CP.fresh_spec_vars qvars in
	                  let st = List.combine qvars ws in
	                  let baref = mkBase qh qp qt qfl qpr qb pos in
	                  let new_baref = subst st baref in
	                  let new_ctx = Ctx {estate with es_evars = ws @ estate.es_evars} in
	                  let tmp_rs, tmp_prf = heap_entail_split_rhs_phases prog is_folding  new_ctx new_baref drop_read_phase pos
	                  in
	                  (match tmp_rs with
		                | FailCtx _ -> (tmp_rs, tmp_prf)
		                | SuccCtx sl ->
		                      let prf = mkExRight ctx_0 conseq qvars ws tmp_prf in
		                      let _ = List.map (redundant_existential_check ws) sl in
		                      let res_ctx =
		                        if !Globals.elim_exists then List.map elim_exists_ctx sl
		                        else sl in
		                      (SuccCtx res_ctx, prf))
	            | _ -> report_error no_pos ("[solver.ml]: No disjunction on the RHS should reach this level\n")
	        end
      end
    | _ -> report_error no_pos ("[solver.ml]: No disjunctive context should reach this level\n")


and eliminate_exist_from_LHS qvars qh qp qt qfl qpr qb pos estate =  
  (* eliminating existential quantifiers from the LHS *)
  (* ws are the newly generated fresh vars for the existentially quantified vars in the LHS *)
  let ws = CP.fresh_spec_vars qvars in
  let st = List.combine qvars ws in
  let baref = mkBase qh qp qt qfl qpr qb pos in
  let new_baref = subst st baref in
  (* new ctx is the new context after substituting the fresh vars for the exist quantified vars *)
  let new_ctx = Ctx {estate with
      es_formula = new_baref;
      es_ante_evars = ws @ estate.es_ante_evars;
      es_unsat_flag = false;} 
  in new_ctx

and heap_n_pure_entail(*_debug*) prog is_folding  ctx0 conseq h p func drop_read_phase pos : (list_context * proof) =
  Gen.Debug.no_2 "heap_n_pure_entail" (Cprinter.string_of_context) Cprinter.string_of_h_formula
      (fun (lc,_) -> match lc with FailCtx _ -> "Not OK" | SuccCtx _ -> "OK")  (fun ctx0 h -> heap_n_pure_entail_x prog is_folding  ctx0 conseq h p func drop_read_phase pos) ctx0 h 

and heap_n_pure_entail_1 prog is_folding  ctx0 conseq h p func drop_read_phase pos = 
  print_string "tracing heap_n_pure_entail_1\n"; (heap_n_pure_entail prog is_folding  ctx0 conseq h p func drop_read_phase pos)

and heap_n_pure_entail_2 prog is_folding  ctx0 conseq h p func drop_read_phase pos = 
  print_string "tracing heap_n_pure_entail_2\n"; (heap_n_pure_entail prog is_folding  ctx0 conseq h p func drop_read_phase pos)

and heap_n_pure_entail_x  
      (prog : prog_decl) 
      (is_folding : bool) 
      
      (ctx0 : context) 
      (conseq : formula) 
      (h : h_formula) 
      p
      func
      (drop_read_phase : bool)
      pos : (list_context * proof) =

  (* let _  = print_string("*************************************************\n") in *)
  (* let _ = print_string("entailing the heap first:\n") in *)
  (* let _  = print_string("*************************************************\n") in *)
  let entail_h_ctx, entail_h_prf = heap_entail_split_lhs_phases prog is_folding  ctx0 (func h (MCP.mkMTrue pos)) (contains_mutable_h_formula h) pos in
  match entail_h_ctx with
    | FailCtx _ -> (entail_h_ctx, entail_h_prf)
    | SuccCtx(cl) ->
	      (* let _  = print_string("*************************************************\n") in *)
	      (* let _ = print_string("entailing the pure:\n") in *)
	      (* let _  = print_string("*************************************************\n") in *)
          let entail_p = List.map 
	        (fun c -> one_ctx_entail prog is_folding  c conseq func p pos) cl  
          in
          let entail_p_ctx, entail_p_prf = List.split entail_p in
          let entail_p_prf = mkContextList cl (Cformula.struc_formula_of_formula conseq pos) entail_p_prf in
          let entail_p_ctx = fold_context_left entail_p_ctx in 
          (entail_p_ctx, entail_p_prf)

and one_ctx_entail prog is_folding  c conseq func p pos : (list_context * proof) = 
  (match c with 
    | Ctx(estate) -> 
          let new_conseq = subst_avoid_capture (fst estate.es_subst) (snd estate.es_subst) (func HTrue p) in
          let aux_conseq_from_fold = subst_avoid_capture (fst estate.es_subst) (snd estate.es_subst) (func HTrue (MCP.mix_of_pure estate.es_aux_conseq)) in
          let new_conseq = CF.mkStar new_conseq aux_conseq_from_fold Flow_combine pos in
          heap_entail_conjunct prog is_folding  c new_conseq pos
    | OCtx (c1, c2) -> 
          let cl1, prf1 = one_ctx_entail prog is_folding  c1 conseq func p pos in
          let cl2, prf2 = one_ctx_entail prog is_folding  c2 conseq func p pos in
          let entail_p_ctx = Cformula.or_list_context cl1 cl2  in 
          let entail_p_prf = 
	        match entail_p_ctx with
	          | FailCtx _ -> mkContextList [] (Cformula.struc_formula_of_formula conseq pos) ([prf1]@[prf2]) 
	          | SuccCtx cl -> mkContextList cl (Cformula.struc_formula_of_formula conseq pos) ([prf1]@[prf2]) 
          in
          (entail_p_ctx, entail_p_prf))

and heap_entail_rhs_read_phase prog is_folding  ctx0 h1 h2 h3 func pos =
  (* entail the read phase heap *)
  (* let _ = print_string("************************************************************************\n") in *)
  (* let _ = print_string("split_rhs: entail rd phase h1 = " ^ (Cprinter.string_of_h_formula h1) ^ "\n") in *)
  (* let _ = print_string("************************************************************************\n") in *)
  let new_conseq =
    if (is_true h2 && is_true h3) then
      func h1 (MCP.mkMTrue pos) 
    else func h1 (MCP.mkMTrue pos)
  in
  let (after_rd_ctx, after_rd_prf) = 
    heap_entail_split_lhs_phases prog is_folding  ctx0 new_conseq (contains_mutable new_conseq) pos 
  in (after_rd_ctx, after_rd_prf)

and heap_entail_rhs_write_phase prog is_folding  after_rd_ctx after_rd_prf conseq h1 h2 h3 func drop_read_phase pos = 
  match after_rd_ctx with
    | FailCtx _ -> (after_rd_ctx, after_rd_prf)
    | SuccCtx (cl) -> 
          (* entail the write phase *)
          (* let _ = print_string("************************************************************************\n") in *)
          (* let _ = print_string("split_rhs: entail wr phase h2 = " ^ (Cprinter.string_of_h_formula h2) ^ "\n") in *)
          (* let _ = print_string("************************************************************************\n") in *)
          let drop_read_phase = 
	        if (contains_mutable_h_formula h2) or (contains_mutable_h_formula h3)
	        then true
	        else false
          in
          let new_conseq =
	        if (is_true h3) then
	          (func h2 (MCP.mkMTrue pos)) 
	        else
	          (func h2 (MCP.mkMTrue pos))
          in
          let after_wr_ctx, after_wr_prfs =
	        if not(is_true h2) then
	          let after_wr = List.map (fun c -> heap_entail_split_lhs_phases prog is_folding  c new_conseq drop_read_phase pos) cl in
	          let after_wr_ctx, after_wr_prfs = List.split after_wr in
	          let after_wr_prfs = mkContextList cl (Cformula.struc_formula_of_formula conseq pos) after_wr_prfs in
	          let after_wr_ctx = fold_context_left after_wr_ctx in 
	          (after_wr_ctx, after_wr_prfs)
	        else 
	          (after_rd_ctx, after_rd_prf)
          in (after_wr_ctx, after_wr_prfs)

and heap_entail_rhs_nested_phase prog is_folding  after_wr_ctx after_wr_prfs conseq h1 h2 h3 func drop_read_phase pos = 
  match after_wr_ctx with
    |FailCtx _ ->  (after_wr_ctx, after_wr_prfs)
    | SuccCtx (cl) -> 
	      let (ctx, prf) =
	        (match h3 with
	          | HTrue -> 
	                (after_wr_ctx, after_wr_prfs)
	          | _ ->
	                (* let _ = print_string("************************************************************************\n") in *)
	                (* let _ = print_string("entail rhs h3 = " ^ (Cprinter.string_of_h_formula h3) ^ "\n") in *)
	                (* let _ = print_string("************************************************************************\n") in *)
	                if (CF.contains_phase h3) then
		              let after_nested_phase = List.map (fun c -> heap_entail_split_rhs_phases prog is_folding  c (func h3 (MCP.mkMTrue pos)) drop_read_phase pos) cl in
		              let after_nested_phase_ctx, after_nested_phase_prfs = List.split after_nested_phase in
		              let after_nested_phase_prfs = mkContextList cl (Cformula.struc_formula_of_formula conseq pos) after_nested_phase_prfs in
		              let after_nested_phase_ctx = fold_context_left after_nested_phase_ctx in
		              (after_nested_phase_ctx, after_nested_phase_prfs)
	                else
		              let after_nested_phase = List.map (fun c -> heap_entail_split_lhs_phases prog is_folding  c (func h3 (MCP.mkMTrue pos)) drop_read_phase pos) cl in
		              let after_nested_phase_ctx, after_nested_phase_prfs = List.split after_nested_phase in
		              let after_nested_phase_prfs = mkContextList cl (Cformula.struc_formula_of_formula conseq pos) after_nested_phase_prfs in
		              let after_nested_phase_ctx = fold_context_left after_nested_phase_ctx in
		              (after_nested_phase_ctx, after_nested_phase_prfs)
	        )
	      in (ctx, prf)

(* some helper methods *)
and insert_ho_frame_in2_formula_debug f ho = 
  Gen.Debug.no_2 "insert_ho_frame_in2_formula"
	  Cprinter.string_of_formula
	  (*Cprinter.string_of_h_formula*)
	  (fun _ -> "?")
	  Cprinter.string_of_formula
	  insert_ho_frame_in2_formula f ho

(* insert an higher order frame into a formula *)
and insert_ho_frame_in2_formula f ho_frame = 
  match f with
    | Base({formula_base_heap = h;
	  formula_base_pure = p;
	  formula_base_type = t;
	  formula_base_flow = fl;
	  formula_base_perm = pr;
	  formula_base_branches = b;
	  formula_base_label = l;
	  formula_base_pos = pos}) ->
	      mkBase (ho_frame h) p  t fl pr b  pos
    | Exists({formula_exists_qvars = qvars;
	  formula_exists_heap = h;
	  formula_exists_pure = p;
	  formula_exists_type = t;
	  formula_exists_flow = fl;
	  formula_exists_perm = pr;
	  formula_exists_branches = b;
	  formula_exists_label = l;
	  formula_exists_pos = pos}) ->
	      mkExists qvars (ho_frame h) p t fl pr b pos
    | Or({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos;}) ->
	      let new_f1 = insert_ho_frame_in2_formula f1 ho_frame in
	      let new_f2 = insert_ho_frame_in2_formula f2 ho_frame in
	      mkOr new_f1 new_f2 pos

and insert_ho_frame ctx ho_frame =
  match ctx with
    | Ctx(f) ->
	      Ctx {f with es_formula =  insert_ho_frame_in2_formula f.es_formula ho_frame;}
    | OCtx(c1, c2) -> OCtx(insert_ho_frame c1 ho_frame, insert_ho_frame c2 ho_frame)

and choose_not_true_heap h1 h2 h3 = 
  if ((is_true h1) && (is_true h2)) then h3
  else if ((is_true h1) && (is_true h3)) then h2
  else h1

(* swaps the heap in f by h; returns the new formula and the extracted heap *)
and swap_heap (f : formula) (new_h : h_formula) pos : (formula * h_formula) = 
  match f with
    | Base (bf) ->
	      let (h, p, fl, pr, b, t) = CF.split_components f in
	      (CF.mkBase new_h p t fl pr b pos, h)
    | Exists({formula_exists_qvars = qvars;
	  formula_exists_heap = h;
	  formula_exists_pure = p;
	  formula_exists_perm = pr;
	  formula_exists_type = t;
	  formula_exists_flow = fl;
	  formula_exists_branches = b;
	  formula_exists_label = l;
	  formula_exists_pos = pos }) -> 
	      (CF.mkExists qvars new_h p t fl pr b pos, h)
    | _ -> report_error no_pos ("solver.ml: No LHS disj should reach this point\n  ")


and heap_entail_split_lhs_phases(*_debug*)
      p is_folding  ctx0 conseq d
      pos : (list_context * proof) =
  Gen.Debug.no_2 "heap_entail_split_lhs_phases"
      (Cprinter.string_of_context)
      (fun _ -> "RHS")
      (* (Cprinter.string_of_formula) *)
      (fun _ -> "OUT")
      (fun ctx0 conseq -> heap_entail_split_lhs_phases_x p is_folding  ctx0 conseq d pos) ctx0 conseq

(* entailment method for splitting the antecedent *)
and heap_entail_split_lhs_phases_x
      (prog : prog_decl) 
      (is_folding : bool) 
      
      (ctx0 : context) 
      (conseq : formula) 
      (drop_read_phase : bool)
      pos : (list_context * proof) =

  Debug.devel_pprint ("heap_entail_split_lhs_phases: 
                            \nante:\n"
  ^ (Cprinter.string_of_context ctx0)
  ^ "\nconseq:\n"
  ^ (Cprinter.string_of_formula conseq)) pos;

    (***** main helper method ******)
    (* called for both formula base and formula exists *)
    let rec helper_lhs h func : (list_context * proof) = 
      (* split h such that:
         h1 = rd phase
         h2 = write phase
         h3 = nested phase 
      *)
      let h1, h2, h3 = split_phase(*_debug_lhs*) h in
      (* let _ = print_string("heap_entail_split_lhs: splitting h into:\n h1 (lhs) = " ^ (Cprinter.string_of_h_formula h1) ^ "\n h2 (lhs) = " ^ (Cprinter.string_of_h_formula h2) ^ "\n h3 (lhs) = " ^ (Cprinter.string_of_h_formula h3) ^ "\n") in *)

      if ((is_true h1) && (is_true h3))
        or ((is_true h2) && (is_true h3))
      then
        (* lhs contains only one phase (no need to split) *)
        let new_ctx = CF.set_context_formula ctx0 (func (choose_not_true_heap h1 h2 h3)) in
	    (* in this case we directly call heap_entail_conjunct *)
        let final_ctx, final_prf = heap_entail_conjunct prog is_folding  new_ctx conseq pos in
	    match final_ctx with
	      | SuccCtx(cl) ->
	            (* substitute the holes due to the temporary removal of matched immutable nodes *) 
	            (* let _ = print_string("Substitute the imm holes \n") in *)
	            let cl1 = List.map Context.subs_crt_holes_ctx cl in
		        (SuccCtx(cl1), final_prf)
	      | FailCtx _ -> (final_ctx, final_prf)
      else
        if ((is_true h1) && (is_true h2)) then
	      (* only the nested phase is different from true;*)
	      let new_ctx = CF.set_context_formula ctx0 (func h3) in
	      let final_ctx, final_prf = 
	        (* we must check whether this phase contains other nested phases *)
	        if not(contains_phase h3) then
	          (* no other nested phases within h3 *)
	          (* direct call to heap_entail_conjunct *)
	          heap_entail_conjunct prog is_folding  new_ctx conseq pos
	        else
	          (* we need to recursively split the phases nested in h3 *)
	          let _ = print_string("\n\nRecursive call to heap_entail_split_lhs_phases\n") in
	          heap_entail_split_lhs_phases prog is_folding  new_ctx conseq drop_read_phase pos
	      in
	      match final_ctx with
	        | SuccCtx(cl) ->
		          (* substitute the holes due to the temporary removal of matched immutable nodes *) 
		          (* let _ = print_string("Substitute the holes\n") in *)
		          let cl1 = List.map Context.subs_crt_holes_ctx cl in
		          (SuccCtx(cl1), final_prf)
	        | FailCtx _ -> (final_ctx, final_prf)

        else
	      (* lhs contains multiple phases *)
	      (******************************************************)
	      (****** the first entailment uses h1 as lhs heap ******)
	      (******************************************************)
	      let lhs_rd = func h1 in
	      let rd_ctx = CF.set_context_formula ctx0 lhs_rd in
	      Debug.devel_pprint ("heap_entail_split_lhs_phases: 
                            \ncall heap_entail_conjunct with lhs = reading phase\n") pos;
	      (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)
	      (* let _ = print_string("split_lhs: entail using h1 = " ^ (Cprinter.string_of_h_formula h1) ^ "\n") in *)
	      (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)


	      let (with_rd_ctx, with_rd_prf) = heap_entail_conjunct prog is_folding  rd_ctx conseq pos in
	      let with_rd_ctx = 
	        (match with_rd_ctx with
              | FailCtx _ -> with_rd_ctx
	          | SuccCtx (cl) -> 
		            (* substitute the holes due to the temporary removal of matched immutable nodes *) 
		            (* let _ = print_string("Substitute the holes \n") in *)
		            let cl1 = List.map Context.subs_crt_holes_ctx cl in
		            (* in case of success, put back the frame consisting of h2*h3 *)
		            let cl2 = List.map (fun x -> insert_ho_frame x (fun f -> CF.mkPhaseH f (CF.mkStarH_nn h2 h3 pos) pos)) cl1 in
		            SuccCtx(cl2))
	      in

	      (*******************************************************)
	      (****** the second entailment uses h2 as lhs heap ******)
	      (*******************************************************)
	      (* push h3 as a continuation in the current ctx *)
	      let new_ctx = Context.push_cont_ctx h3 ctx0 in
	      (* set the es_formula to h2 *)
	      let f_h2 = func h2 in
	      let wr_ctx = CF.set_context_formula new_ctx f_h2 in
	      Debug.devel_pprint ("heap_entail_split_lhs_phases: 
                            \ncall heap_entail_conjunct with lhs = writing phase\n") pos;

	      (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)
	      (* let _ = print_string("split_lhs: entail using h2 = " ^ (Cprinter.string_of_h_formula h2) ^ "\n") in *)
	      (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)


	      let (with_wr_ctx, with_wr_prf) = heap_entail_conjunct prog is_folding  wr_ctx conseq pos in
	      (******************************************************)
	      (****** the third entailment uses h3 as lhs heap ******)
	      (******************************************************)
	      (* todo: check whether the conseq != null (?)*)
	      (* check if there is need for another entailment that uses the continuation h3 *)
	      let (final_ctx, final_prf) = 
	        match with_wr_ctx with
		      | SuccCtx(cl) -> 
		            (* h2 was enough, no need to use h3 *)
		            (* substitute the holes due to the temporary removal of matched immutable nodes *) 
		            (* let _ = print_string("Substitute the holes \n") in *)
		            let cl = List.map Context.subs_crt_holes_ctx cl in
		            (* put back the frame consisting of h1 and h3 *)
		            (* first add the frame []*h3 *) 
		            let cl = List.map (fun x -> insert_ho_frame x (fun f -> CF.mkStarH_nn f h3 pos)) cl in
		            let cl = 
		              if not(CF.contains_mutable conseq) && not(drop_read_phase) then
			            (* next add the frame h1;[]*)
			            List.map (fun x -> insert_ho_frame x (fun f -> CF.mkPhaseH h1 f pos)) cl 
		              else
			            (* else drop the read phase (don't add back the frame) *)
			            let xpure_rd_0, _, _, memset_rd = xpure_heap 2 prog h1 0 (MCP.mkMTrue pos) Cpr.stub_sol in
			            let xpure_rd_1, _, _, memset_rd = xpure_heap 2 prog h1 1 (MCP.mkMTrue pos) Cpr.stub_sol in
			            (* add the pure info for the dropped reading phase *)
			            List.map 
			                (Cformula.transform_context 
			                    (fun es -> 
				                    Ctx{es with 
					                    (* add xpure0 directly to the state formula *)
					                    es_formula = mkStar es.es_formula (formula_of_mix_formula xpure_rd_0 (Cperm.mkTrue pos) pos) Flow_combine pos;
					                    (* store xpure_1 of the dropped phase for the case it is needed later during the entailment (i.e. xpure0 is not enough) *)
					                    es_aux_xpure_1 = MCP.merge_mems es.es_aux_xpure_1 xpure_rd_1 true; 
				                    })) cl
		            in
 		            (SuccCtx(cl), with_wr_prf)
		      | FailCtx(ft) -> 
		            (* insuccess when using lhs = h2; need to try the continuation *)
		            match h3 with
		              | HTrue ->
			                (* h3 = true and hence it wont help *)
			                (with_wr_ctx, with_wr_prf)
		              | _ ->
			                heap_entail_with_cont  prog is_folding  ctx0 conseq ft h1 h2 h3 with_wr_ctx with_wr_prf func drop_read_phase pos

	      in
	      (* union of states *)
	      (*	let _ = print_string("compute final answer\n") in*)
	      ((fold_context_left [with_rd_ctx; final_ctx]),( mkOrRight ctx0 conseq [with_rd_prf; final_prf]))		
		      (*  end of helper method *)

    (* handles the possible ent continuations *)
    and heap_entail_with_cont  
          (prog : prog_decl) 
          (is_folding : bool) 
          
          (ctx0 : context) 
          (conseq : formula) 
          (ft : fail_type)
          (h1 : h_formula)
          (h2 : h_formula)
          (h3 : h_formula)
          (with_wr_ctx : list_context) 
          (with_wr_prf : proof)
          func
          (drop_read_phase : bool)
          pos : (list_context * proof) =
      match ft with
        | Continuation(fc) ->
	          begin
	            (* check if there is any continuation in the continuation list es_cont *)
	            let lhs = fc.fc_current_lhs in
	            if (lhs.es_cont = []) then
	              (* no continuation *)
	              (* ---TODO:  need to enable folding --- *)
	              (with_wr_ctx, with_wr_prf)
	            else 
	              (* pop the continuation record *)
	              (* the cont record contains (actual continuation to be used on the lhs, the failing lhs) *)
	              (* actually, we already know the continuation is h3 *)
	              let _, lhs = Context.pop_cont_es lhs in
		          (* retrieve the current conseq from the failed context *)				    
	              let conseq = fc.fc_current_conseq in
		          (* swap the current lhs heap (keep it as frame) and the continuation h3 *)
	              let new_f, h2_rest = swap_heap lhs.es_formula h3 pos in
		          (* create the current context containing the current estate *)
	              let cont_ctx = Ctx({lhs with es_formula = new_f;}) in
	              (* let cont_ctx_list = SuccCtx([cont_ctx]) in *)
		          (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)
		          (* let _ = print_string("split_lhs: entail using h3 = " ^ (Cprinter.string_of_h_formula h3) ^ "\n") in *)
		          (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)

	              let after_wr_ctx, after_wr_prf =
		            if (CF.contains_phase h3) then
		              (Debug.devel_pprint ("heap_entail_split_lhs_phases: \ncall heap_entail_split_lhs_phase for the continuation\n") pos;
		              heap_entail_split_lhs_phases prog is_folding  cont_ctx conseq drop_read_phase pos)
		            else
		              (Debug.devel_pprint ("heap_entail_split_lhs_phases: \ncall heap_entail_conjunct for the continuation\n") pos;
		              heap_entail_conjunct prog is_folding  cont_ctx conseq pos)
	              in
		          (match after_wr_ctx with
		            | FailCtx _ -> (after_wr_ctx, after_wr_prf)
		            | SuccCtx (cl) -> 
		                  (* substitute the holes due to the temporary removal of matched immutable nodes *) 
		                  (* let _ = print_string("Substitute the holes\n") in *)
		                  let cl = List.map Context.subs_crt_holes_ctx cl in
			              (* in case of success, put back the frame consisting of h1 and what's left of h2 *)
			              (* first add the frame h2_rest*[] *) 
		                  let cl = List.map (fun x -> insert_ho_frame x (fun f -> CF.mkStarH_nn h2_rest f pos)) cl in
			              (* next add the frame h1;[]*)
		                  let cl =
			                if not(CF.contains_mutable conseq)  && not(drop_read_phase) then
			                  List.map (fun x -> insert_ho_frame x (fun f -> CF.mkPhaseH h1 f pos)) cl 
			                else
			                  (* drop read phase *)
			                  let xpure_rd_0, _, _, memset_rd = xpure_heap 3 prog h1 0 (MCP.mkMTrue pos) Cpr.stub_sol in
			                  let xpure_rd_1, _, _, memset_rd = xpure_heap 3 prog h1 1 (MCP.mkMTrue pos) Cpr.stub_sol in
			                  (* add the pure info corresponding to the dropped reading phase *)
			                  List.map 
			                      (Cformula.transform_context 
				                      (fun es -> 
				                          Ctx{es with 
					                          (* add xpure0 directly to the state formula *)
					                          es_formula = mkStar es.es_formula (formula_of_mix_formula xpure_rd_0 (Cperm.mkTrue pos) pos) Flow_combine pos;
					                          (* store xpure_1 of the dropped phase for the case it is needed later during the entailment (i.e. xpure0 is not enough) *)
					                          es_aux_xpure_1 = MCP.merge_mems es.es_aux_xpure_1 xpure_rd_1 true; 
					                      })) cl

		                  in
			              (SuccCtx(cl), after_wr_prf)
		          )
	          end
        | Or_Continuation(ft1, ft2) ->
	          let ctx1, prf1 = heap_entail_with_cont prog is_folding  ctx0 conseq ft1 h1 h2 h3 with_wr_ctx with_wr_prf func drop_read_phase pos in
	          let ctx2, prf2 = heap_entail_with_cont prog is_folding  ctx0 conseq ft2 h1 h2 h3 with_wr_ctx with_wr_prf func drop_read_phase pos in
	          (* union of states *)
	          ((fold_context_left [ctx1; ctx2]),( mkOrRight ctx0 conseq [prf1; prf2]))		
        | _ -> 
	          (* no continuation -> try to discharge the conseq by using h3 as lhs and h2*[] as frame *)
	          (* create the new ctx *)
	          let lhs_wr = func h3 in
	          let wr_ctx = CF.set_context_formula ctx0 lhs_wr in
	          let (with_wr_ctx, with_wr_prf) = heap_entail_split_lhs_phases prog is_folding  wr_ctx conseq drop_read_phase pos in
	          let (with_wr_ctx, with_wr_prf) = 
	            (match with_wr_ctx with
	              | FailCtx _ -> (with_wr_ctx, with_wr_prf)
	              | SuccCtx (cl) -> 
		                (* substitute the holes due to the temporary removal of matched immutable nodes *) 
		                (* let _ = print_string("Substitute the holes \n") in *)

		                let cl = List.map Context.subs_crt_holes_ctx cl in   
		                (* in case of success, put back the frame consisting of h1;h2*[] *)
		                (* first add the frame h2*[] *) 
		                let cl = List.map (fun x -> insert_ho_frame x (fun f -> CF.mkStarH_nn h2 f pos)) cl in
                        (* next add the frame h1;[]*)
		                let cl = List.map (fun x -> insert_ho_frame x (fun f -> CF.mkPhaseH h1 f pos)) cl in
		                (SuccCtx(cl), with_wr_prf)
	            )
	          in (with_wr_ctx, with_wr_prf)
    in

    (* main method *)
    let lhs = CF.formula_of_context ctx0
    in
    match lhs with 
      | Base(bf) -> 
	        let (h, p, fl, pr, b, t) = CF.split_components lhs in
	        helper_lhs h (fun xh -> CF.mkBase xh p t fl pr b pos)

      | Exists({formula_exists_qvars = qvars;
	    formula_exists_heap = h;
        formula_exists_pure = p;
        formula_exists_type = t;
		formula_exists_perm = pr;
        formula_exists_flow = fl;
        formula_exists_branches = b;
        formula_exists_label = l;
        formula_exists_pos = pos }) -> 
	        helper_lhs h (fun xh -> CF.mkExists qvars xh p t fl pr b pos)
      | _ -> report_error no_pos ("[solver.ml]: No disjunction on the LHS should reach this level\n")



(* check the entailment of two conjuncts  *)
(* return value: if fst res = true, then  *)
(* snd res is the residual. Otherwise     *)
(* snd res is the constraint that causes  *)
(* the check to fail.                     *)

and heap_entail_conjunct (prog : prog_decl) (is_folding : bool)  (ctx0 : context) (conseq : formula) pos : (list_context * proof) = 
  Gen.Debug.no_2 "heap_entail_conjunct" Cprinter.string_of_formula Cprinter.string_of_context (fun _ -> "?")
      (fun c _-> heap_entail_conjunct_x prog is_folding  ctx0 c pos) conseq ctx0

and heap_entail_conjunct_x (prog : prog_decl) (is_folding : bool)  (ctx0 : context) (conseq : formula) pos : (list_context * proof) =
  (* PRE : BOTH LHS and RHS are not disjunctive *)
  Debug.devel_pprint ("heap_entail_conjunct:"
  ^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx0)
  ^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq)) pos;
    (* <<<<<<< solver.ml *)
    heap_entail_conjunct_helper prog is_folding  ctx0 conseq pos
        (* check the entailment of two conjuncts  *)
        (* return value: if fst res = true, then  *)
        (* snd res is the residual. Otherwise     *)
        (* snd res is the constraint that causes  *)
        (* the check to fail.                     *)
and heap_entail_conjunct_helper (prog : prog_decl) (is_folding : bool)  (ctx0 : context) (conseq : formula) pos : (list_context * proof) =
  Debug.devel_pprint ("heap_entail_conjunct_helper:"
  ^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx0)
  ^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq)) pos;
    match ctx0 with
      | OCtx _ -> report_error pos ("heap_entail_conjunct_helper: context is disjunctive or fail!!!")
      | Ctx estate -> begin
	      let ante = estate.es_formula in
	      match ante with
	        | Exists ({formula_exists_qvars = qvars;
		      formula_exists_heap = qh;
		      formula_exists_pure = qp;
			  formula_exists_perm = qpr;
		      formula_exists_type = qt;
		      formula_exists_flow = qfl;
		      formula_exists_branches = qb;
		      formula_exists_pos = pos}) ->
		          (* eliminating existential quantifiers from the LHS *)
		          (* ws are the newly generated fresh vars for the existentially quantified vars in the LHS *)
		          let ws = CP.fresh_spec_vars qvars in
		          (*--- 09.05.2008 *)
		          (*let _ = (print_string ("\n[solver.ml, line 1183]: fresh name = " ^ (Cprinter.string_of_spec_var_list ws) ^ "!!!!!!!!!!!\n")) in*)
		          (*09.05.2008 ---*)
		          let st = List.combine qvars ws in
		          let baref = mkBase qh qp qt qfl qpr qb pos in
		          let new_baref = subst st baref in
		          (* new ctx is the new context after substituting the fresh vars for the exist quantified vars *)
		          let new_ctx = Ctx {estate with
				      es_formula = new_baref;
				      es_ante_evars = ws @ estate.es_ante_evars;
				      es_unsat_flag = false;} in
		          (* call the entailment procedure for the new context - with the existential vars substituted by fresh vars *)
		          let rs, prf1 = heap_entail_conjunct_helper prog is_folding  new_ctx conseq pos in
		          (* --- added 11.05.2008 *)
		          let new_rs =
		            if !Globals.wrap_exist then
		              (* the fresh vars - that have been used to substitute the existenaltially quantified vars - need to be existentially quantified after the entailment *)
		              (add_exist_vars_to_ctx_list rs ws)
		            else
		              rs
		          in
		          (* log the transformation for the proof tracere *)
		          let prf = mkExLeft ctx0 conseq qvars ws prf1 in
		          (new_rs, prf)
	        | _ -> begin
		        match conseq with
		          | Exists ({formula_exists_qvars = qvars;
			        formula_exists_heap = qh;
			        formula_exists_pure = qp;
			        formula_exists_type = qt;
			        formula_exists_flow = qfl;
					formula_exists_perm = qpr;
			        formula_exists_branches = qb;
			        formula_exists_pos = pos}) ->
		                (* quantifiers on the RHS. Keep them for later processing *)
		                let ws = CP.fresh_spec_vars qvars in
		                let st = List.combine qvars ws in
		                let baref = mkBase qh qp qt qfl qpr qb pos in
		                let new_baref = subst st baref in
		                let new_ctx = Ctx {estate with es_evars = ws @ estate.es_evars} in
		                let tmp_rs, tmp_prf = heap_entail_conjunct_helper prog is_folding  new_ctx new_baref pos in
			            (match tmp_rs with
			              | FailCtx _ -> (tmp_rs, tmp_prf)
			              | SuccCtx sl ->
			                    let prf = mkExRight ctx0 conseq qvars ws tmp_prf in
				                (*added 09-05-2008 , by Cristian, checks that after the RHS existential elimination the newly introduced variables will no appear in the residue hence no need to quantify*)
			                    let _ = List.map (redundant_existential_check ws) sl in
			                    let res_ctx =
				                  if !Globals.elim_exists then List.map elim_exists_ctx sl
				                  else sl in
				                (SuccCtx res_ctx, prf))
		          | _ ->
		                let h1, p1, fl1, pr1, br1, t1 = split_components ante in
		                let h2, p2, fl2, pr2, br2, t2 = split_components conseq in
			            (* let _ = print_string "pp 1\n" in*)
			            if (isAnyConstFalse ante)&&(CF.subsume_flow_ff fl2 fl1) then 
			              let _ = print_string ("got: "^(Cprinter.string_of_formula ante)^"|-"^(Cprinter.string_of_formula conseq)^"\n\n") in
			              (SuccCtx [false_ctx fl1 pos], UnsatAnte)
			            else					  
			              (*  let _ = print_string "pp 2\n" in*)
			              (* let _ = print_string ("bol : "^(string_of_bool ((CF.is_false_flow fl2.formula_flow_interval)))^"\n") in*)
			              if (not(CF.is_false_flow fl2.formula_flow_interval)) && not(CF.subsume_flow_ff fl2 fl1) then begin
			                Debug.devel_pprint ("heap_entail_conjunct_helper: "
						    ^ "conseq has an incompatible flow type"
						    ^ "\ncontext:\n"
						    ^ (Cprinter.string_of_context ctx0)
						    ^ "\nconseq:\n"
						    ^ (Cprinter.string_of_formula conseq)) pos;
			                (CF.mkFailCtx_in (Basic_Reason ({fc_message ="incompatible flow type"; 
							fc_current_lhs = estate;
							fc_orig_conseq = struc_formula_of_formula conseq pos;
							fc_prior_steps = estate.es_prior_steps;
							fc_current_conseq = CF.formula_of_heap HFalse pos;
							fc_failure_pts =[];})), UnsatConseq) 
			              end
			              else 
			                match h2 with
			                  | HFalse (* -> (--[], UnsatConseq)  entailment fails *)
			                  | HTrue -> begin
				                  Debug.devel_pprint ("heap_entail_conjunct_helper: "
						          ^ "conseq has an empty heap component"
						          ^ "\ncontext:\n"
						          ^ (Cprinter.string_of_context ctx0)
						          ^ "\nconseq:\n"
						          ^ (Cprinter.string_of_formula conseq)) pos;
				                  let b1 = { formula_base_heap = h1;
					              formula_base_pure = p1;
					              formula_base_type = t1;
								  formula_base_perm = pr1;
					              (* formula_base_imm = contains_immutable_h_formula h1; *)
					              formula_base_flow = fl1;
					              formula_base_branches = br1;
					              formula_base_label = None;
					              formula_base_pos = pos } in
				                  (* 23.10.2008 *)
				                  (*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
				                  (* at the end of an entailment due to the epplication of an universal lemma, we need to move the explicit instantiation to the antecedent  *)
				                  (* Remark: for universal lemmas we use the explicit instantiation mechanism,  while, for the rest of the cases, we use implicit instantiation *)
				                  (*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
				                  let ctx, proof = 
									let perm_impl = Cperm.imply (estate.es_evars@estate.es_gen_expl_vars@estate.es_ivars) in
									if (perm_impl pr1 pr2) then heap_entail_empty_rhs_heap prog is_folding  estate b1 p2 br2 pr2 pos 
									else 
                    ( Debug.devel_pprint ("heap_entail_conjunct_helper: failed in proving the permissions implication") pos;
                  (CF.mkFailCtx_in (Basic_Reason (mkFailContext "failed in entailing perm formulas" estate conseq None pos )), Failure)) in
				                  (* let new_ctx = *)
				                  (*   if  then ((\*print_string ("YES Expl inst!!\n");*\) move_lemma_expl_inst_ctx_list ctx p2) *)
				                  (*   else ((\*print_string ("NO Expl inst!!\n");*\) ctx ) *)
				                  (* in *)
				                  let new_ctx = move_expl_inst_ctx_list ctx p2 pr2 in
				                  (new_ctx, proof)
				                end
			                  | _ -> begin
				                  Debug.devel_pprint ("heap_entail_conjunct_helper: "
						          ^ "conseq has an non-empty heap component"
						          ^ "\ncontext:\n"
						          ^ (Cprinter.string_of_context ctx0)
						          ^ "\nconseq:\n"
						          ^ (Cprinter.string_of_formula conseq)) pos;
				                  let b1 = { formula_base_heap = h1;
					              formula_base_pure = p1;
					              formula_base_type = t1;
								  formula_base_perm = pr1;
					              (* formula_base_imm = contains_immutable_h_formula h1; *)
					              formula_base_branches = br1;
					              formula_base_flow = fl1;
					              formula_base_label = None;
					              formula_base_pos = pos } in
				                  let b2 = { formula_base_heap = h2;
					              formula_base_pure = p2;
					              formula_base_type = t2;
					              (* formula_base_imm = contains_immutable_h_formula h2; *)
					              formula_base_flow = fl2;
								  formula_base_perm = pr2;
					              formula_base_branches = br2;
					              formula_base_label = None;
					              formula_base_pos = pos } in
				                  heap_entail_non_empty_rhs_heap prog is_folding  ctx0 estate ante conseq b1 b2 pos
				                end
	          end
        end

and heap_entail_build_mix_formula_check_a (evars : CP.spec_var list) (ante : MCP.mix_formula) (conseq : MCP.mix_formula) pos : (MCP.mix_formula * MCP.mix_formula) =
  let avars = MCP.mfv ante in
  let sevars = (* List.map CP.to_int_var *) evars in
  let outer_vars, inner_vars = List.partition (fun v -> CP.mem v avars) sevars in
  (*let _ = print_string ("\nheap_entail_build_mix_formula_check: conseq: "^(Cprinter.string_of_mix_formula conseq)) in*)
  let conseq = if !no_RHS_prop_drop then conseq else  MCP.mix_cons_filter conseq MCP.isImplT in
  let tmp1 = (*MCP.memo_pure_push_exists*) elim_exists_mix_formula inner_vars conseq no_pos in
  let tmp1 = MCP.memo_pure_push_exists outer_vars tmp1 in
  (ante,tmp1)

and heap_entail_build_mix_formula_check (evars : CP.spec_var list) (ante : MCP.mix_formula) (conseq : MCP.mix_formula) pos : (MCP.mix_formula * MCP.mix_formula) =
  Gen.Debug.no_3 "heap_entail_build_mix_formula_check_debug"  (fun l -> Cprinter.string_of_spec_var_list l) 
      Cprinter.string_of_mix_formula Cprinter.string_of_mix_formula (fun (_,c )-> Cprinter.string_of_mix_formula c)
      ( fun c1 ante c2 -> heap_entail_build_mix_formula_check_a c1 ante c2 pos) evars ante conseq       


and heap_entail_build_pure_check ev an cq pos =
  Gen.Debug.no_1 "heap_entail_build_pure_check" 
      Cprinter.string_of_pure_formula 
      (fun (f1,f2) -> "f1 = " ^ (Cprinter.string_of_pure_formula f1) ^ "; f2 = " ^ (Cprinter.string_of_pure_formula f2) ^ "\n") 
      (fun cq -> heap_entail_build_pure_check_a ev an cq pos) cq

and heap_entail_build_pure_check_a (evars : CP.spec_var list) (ante : CP.formula) (conseq : CP.formula) pos : (CP.formula * CP.formula) =
  let tmp1 = CP.mkExists evars conseq None no_pos in
  (ante, tmp1)

and xpure_imply (prog : prog_decl) (is_folding : bool)   lhs rhs_p timeout : bool = 
  let imp_subno = ref 0 in
  let estate = lhs in
  let pos = no_pos in
  let r,c = match lhs.es_formula with
    | Or _ -> report_error no_pos ("xpure_imply: encountered Or formula on lhs")
    | Base b ->  (b,lhs)
    | Exists b ->  report_error no_pos ("xpure_imply: encountered Exists formula on lhs")in
	
  (*if (Cperm.imply r.formula_base_perm rhs_p.formula_base_perm) then true 
  else*)
  let lhs_h = r.formula_base_heap in  
  let lhs_p = r.formula_base_pure in
  let lhs_b = r.formula_base_branches in
  let lhs_pr = r.formula_base_perm in
  let _ = reset_int2 () in
  let hx = mkStarH_nn lhs_h estate.es_heap pos in
  let hx,_,_,_ = normalize_frac_heap_w prog hx lhs_p in
 (* if not (is_h_normalized hx lhs_p) then report_error no_pos "xpure_imply: xpuring a non normalized formula" else () ;*)
  (*let nhx,npx,_,_ = normalize_--frac_heap hx lhs_p in*)
  let pr_sol = Cpr.solve_once lhs_pr in
  let xpure_lhs_h, xpure_lhs_h_b, _, memset = xpure_heap 4 prog (*nhx*) hx 1 (*npx*) lhs_p pr_sol in
  let tmp0 = lhs_p (*MCP.merge_mems lhs_p npx lhs_p false*) in
  let tmp1 = MCP.merge_mems tmp0 xpure_lhs_h true in
  let new_ante, new_conseq = heap_entail_build_mix_formula_check (estate.es_evars@estate.es_gen_expl_vars@estate.es_gen_impl_vars) tmp1 
    (MCP.memoise_add_pure_N (MCP.mkMTrue pos) rhs_p) pos in
  let (res,_,_) = imply_mix_formula_no_memo new_ante new_conseq !imp_no !imp_subno (Some timeout) memset in
  (*-- to remove--  
    let new_conseq = solve_ineq new_conseq memset in
    let res,_,_ =  TP.mix_imply_timeout new_ante new_conseq ((string_of_int !imp_no) ^ "." ^ (string_of_int !imp_subno)) timeout in
    Debug.devel_pprint ("IMP #" ^ (string_of_int !imp_no) ^ "." ^ (string_of_int !imp_subno)) no_pos;				
  *)  
  imp_subno := !imp_subno+1;  
  if res = false then
    let branches = Gen.BList.remove_dups_eq (=) (List.map (fun (bid, _) -> bid) (xpure_lhs_h_b @ lhs_b)) in
    let fold_fun2 is_ok branch_id_added =
	  if is_ok then true else
        let tmp1 = MCP.merge_mems 
          (MCP.combine_mix_branch branch_id_added (lhs_p, lhs_b))
          (MCP.combine_mix_branch branch_id_added (xpure_lhs_h, xpure_lhs_h_b)) true in
        let new_ante, new_conseq = heap_entail_build_mix_formula_check (estate.es_evars@estate.es_gen_expl_vars@estate.es_gen_impl_vars) tmp1 
          (MCP.memoise_add_pure_N (MCP.mkMTrue pos) rhs_p) pos in

	    let (res,_,_) = imply_mix_formula_no_memo new_ante new_conseq !imp_no !imp_subno (Some timeout) memset in
	    (* -- to remove --*)
	    (*	let new_conseq = solve_ineq new_conseq memset in
		    let res,_,_ = TP.mix_imply_timeout new_ante new_conseq ((string_of_int !imp_no) ^ "." ^ (string_of_int !imp_subno)) timeout in
		    (Debug.devel_pprint ("IMP #" ^ (string_of_int !imp_no) ^ "." ^ (string_of_int !imp_subno)) no_pos;)*)				
        imp_subno := !imp_subno+1; 
        res 
    in
	List.fold_left fold_fun2 false branches
  else res 

and heap_entail_empty_rhs_heap p i_f es lhs rhs rhsb rhspr pos =
  let pr (e,_) = Cprinter.string_of_list_context e in
  Gen.Debug.no_2 "heap_entail_empty_rhs_heap" (fun c-> Cprinter.string_of_formula(Base c)) Cprinter.string_of_mix_formula pr
      (fun _ _ -> heap_entail_empty_rhs_heap_x p i_f es lhs rhs rhsb rhspr pos) lhs rhs

and heap_entail_empty_rhs_heap_x (prog : prog_decl) (is_folding : bool)  estate lhs (rhs_p:MCP.mix_formula) rhs_p_br rhs_pr pos : (list_context * proof) =
  let imp_subno = ref 1 in
  let lhs_h = lhs.formula_base_heap in
  let lhs_p = lhs.formula_base_pure in
  let lhs_t = lhs.formula_base_type in
  let lhs_fl = lhs.formula_base_flow in
  let lhs_pr = lhs.formula_base_perm in 
  let lhs_b = lhs.formula_base_branches in
  let _ = reset_int2 () in
  let hx = mkStarH_nn lhs_h estate.es_heap pos in
  let hx,_,_,_ = normalize_frac_heap_w prog hx lhs_p in
  (*if not (is_h_normalized hx lhs_p) then report_error no_pos "heap_entail_empty_rhs_heap: xpuring a non normalized formula" else () ;*)
  let curr_lhs_h= hx in
  (*let curr_lhs_h,curr_lhs_p,_,_ = normalize_--frac_heap hx lhs_p in*)
  let pr_sol = Cpr.solve_once lhs_pr in
  let xpure_lhs_h0, xpure_lhs_h0_b, _, memset = xpure_heap 5 prog curr_lhs_h 0 lhs_p pr_sol in
  let xpure_lhs_h1, xpure_lhs_h1_b, _, memset = xpure_heap 5 prog curr_lhs_h 1 lhs_p pr_sol in
  (*let xpure_lhs_h0 = MCP.merge_mems xpure_lhs_h0 curr_lhs_p false in
  let xpure_lhs_h1 = MCP.merge_mems xpure_lhs_h1 curr_lhs_p false in*)
  (* add the information about the dropped reading phases *)
  let xpure_lhs_h1 = MCP.merge_mems xpure_lhs_h1 estate.es_aux_xpure_1 true in
  let xpure_lhs_h1 = if (Cast.any_xpure_1 prog curr_lhs_h) then xpure_lhs_h1 else MCP.mkMTrue no_pos in
  let fold_fun (is_ok,succs,fails) ((branch_id, rhs_p):string*MCP.mix_formula) =
    if (is_ok = false) then (is_ok,succs,fails) else 
      let m_lhs = MCP.combine_mix_branch branch_id (lhs_p, lhs_b) in
      let tmp2 = MCP.merge_mems m_lhs (MCP.combine_mix_branch branch_id (xpure_lhs_h0, xpure_lhs_h0_b)) true in
      let tmp3 = MCP.merge_mems m_lhs (MCP.combine_mix_branch branch_id (xpure_lhs_h1, xpure_lhs_h1_b)) true in
      let exist_vars = estate.es_evars@estate.es_gen_expl_vars@estate.es_ivars(* @estate.es_gen_impl_vars *) in
      let new_ante0, new_conseq0 = heap_entail_build_mix_formula_check exist_vars tmp2 rhs_p pos in
      let new_ante1, new_conseq1 = heap_entail_build_mix_formula_check exist_vars tmp3 rhs_p pos in
	  (* 26.03.2009 simplify the pure part *) 		 
	  (*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)				
	  (* TODO: if xpure 1 is needed, then perform the same simplifications as for xpure 0 *)
	  (*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)				
      let new_ante0 =
        if !Globals.omega_simpl && not(TP.is_mix_bag_constraint new_ante0)&& not(TP.is_mix_list_constraint new_ante0)  then 
          let simp_ante = new_ante0 in
          if !Globals.omega_err = false then simp_ante else (Globals.omega_err := false; new_ante0)	(* reset the error flag *)
        else new_ante0 in
      let new_conseq0 = 
	    if !Globals.omega_simpl && not(TP.is_mix_bag_constraint new_conseq0)&& not(TP.is_mix_list_constraint new_conseq0)  then 
	      let simp_conseq = (Debug.devel_pprint ("simplify the consequent with omega") no_pos;	
		  (*simpl_memo_pure_formula*) new_conseq0) in
	      let simp_conseq1 =  if !Globals.omega_err = false then simp_conseq else (Globals.omega_err := false; new_conseq0)	in 
          (* use the previous conseq , reset the error flag *)
          memo_normalize_to_CNF_new (MCP.memo_arith_simplify simp_conseq1) pos 
	    else new_conseq0 in
      let _ = Debug.devel_pprint ("IMP #" ^ (string_of_int !imp_no) (*^ "." ^ (string_of_int !imp_subno) ^ " with XPure0"*)) no_pos in
	  (* <<<<<<< solver.ml *)
	  (*       let split_conseq = Tpdispatcher.split_conjunctions new_conseq0 in *)
	  (*       let split_ante0 = Tpdispatcher.split_disjunctions new_ante0 in *)
	  (*       let split_ante1 = Tpdispatcher.split_disjunctions new_ante in *)
	  (* 	  (\* first try for xpure 0 and see what conjuncts can be discharged *\) *)
	  (*       let res1,res2,res3 = if (CP.isConstTrue rhs_p) then (true,[],None) else (imply_conj split_ante0 split_ante1 split_conseq memset) in	 *)
	  (* 	  (\* added by cezary  for branches *\) *)
	  (*       let res1,res2,re3 =  *)
	  (* ======= *)
      let split_conseq = (*Tpdispatcher.split_conjunctions*) new_conseq0 in
      let split_ante0 = (*Tpdispatcher.split_disjunctions*) new_ante0 in
      let split_ante1 = new_ante1 in
      let res1,res2,res3 = if (MCP.isConstMTrue rhs_p) then (true,[],None) 
      else (imply_mix_formula split_ante0 split_ante1 split_conseq imp_no memset) in	
      let res1,res2,re3 = 
        if res1 = false && branch_id = "" then
	      let branches = Gen.BList.remove_dups_eq (=) (List.map (fun (bid, _) -> bid) (xpure_lhs_h1_b @ lhs_b)) in
          let fold_fun (is_ok,a2,a3) branch_id_added =
            if is_ok then (is_ok,a2,a3) else
	          let tmp1 = MCP.merge_mems (MCP.combine_mix_branch branch_id_added (xpure_lhs_h1, xpure_lhs_h1_b)) 
                (MCP.combine_mix_branch branch_id_added (lhs_p, lhs_b)) false in
	          let new_ante, new_conseq = heap_entail_build_mix_formula_check (estate.es_evars@estate.es_gen_expl_vars@estate.es_gen_impl_vars) tmp1 rhs_p pos in
		      imp_subno := !imp_subno+1; 
		      (* <<<<<<< solver.ml *)
		      (* 		      Debug.devel_pprint ("IMP #" ^ (string_of_int !imp_no) ^ "." ^ (string_of_int !imp_subno)) no_pos; *)
		      (* 		      TP.imply new_ante new_conseq memset ((string_of_int !imp_no) ^ "." ^ (string_of_int !imp_subno)) *)
		      (* ======= *)
		      (*Debug.devel_pprint ("IMP #" ^ (string_of_int !imp_no) ^ "." ^ (string_of_int !imp_subno)) no_pos;*)
		      (* -- to remove --*)
		      (*		      new_conseq = solve_ineq new_conseq memset in
				              TP.mix_imply new_ante new_conseq ((string_of_int !imp_no) ^ "." ^ (string_of_int !imp_subno))
				              ---*)
		      (imply_mix_formula_no_memo new_ante new_conseq !imp_no !imp_subno None memset)
          in
          List.fold_left fold_fun (false,[],None) branches
        else (res1,res2,res3)
      in
	  (imp_no := !imp_no+1;
	  (res1,res2@succs,res3))  in

  let prf = mkPure estate (CP.mkTrue no_pos) (CP.mkTrue no_pos) true None in
  let memo_r_br = List.map (fun (c1,c2)-> (c1,MCP.memoise_add_pure_N (MCP.mkMTrue pos) c2)) rhs_p_br in
  let (r_rez,r_succ_match, r_fail_match) = List.fold_left fold_fun  (true,[],None) (("", rhs_p) :: memo_r_br) in
  if r_rez then begin
    let res_delta = mkBase lhs_h lhs_p lhs_t lhs_fl lhs_pr lhs_b no_pos in
	if is_folding then begin
	  let es_p, es_br, es_pr = estate.es_pure in
	  let res_es = {estate with es_formula = res_delta; 
		  es_pure = ((MCP.merge_mems rhs_p es_p true),(Cpure.merge_branches es_br rhs_p_br),(Cpr.mkAnd es_pr rhs_pr pos));
		  es_success_pts = (List.fold_left (fun a (c1,c2)-> match (c1,c2) with
			| Some s1,Some s2 -> (s1,s2)::a
			| _ -> a) [] r_succ_match)@estate.es_success_pts;
		  es_unsat_flag = false;} in
	  let res_ctx = Ctx (CF.add_to_estate res_es "folding performed") in
	  Debug.devel_pprint ("heap_entail_empty_heap: folding: formula is valid") pos;
	  Debug.devel_pprint ("heap_entail_empty_heap: folding: res_ctx:\n" ^ (Cprinter.string_of_context res_ctx)) pos;
	  (SuccCtx[res_ctx], prf)
	end else begin
	  let res_ctx = Ctx {estate with es_formula = res_delta;
		  es_success_pts = (List.fold_left (fun a (c1,c2)-> match (c1,c2) with
			| Some s1,Some s2 -> (s1,s2)::a
			| _ -> a) [] r_succ_match)@estate.es_success_pts;} in
	  Debug.devel_pprint ("heap_entail_empty_heap: formula is valid") pos;
	  Debug.devel_pprint ("heap_entail_empty_heap: res_ctx:\n" ^ (Cprinter.string_of_context res_ctx)) pos;
	  (SuccCtx[res_ctx], prf)
	end
  end else begin
    Debug.devel_pprint ("heap_entail_empty_rhs_heap: formula is not valid\n") pos;
    (CF.mkFailCtx_in (Basic_Reason ({
		fc_message = "failed in entailing pure formula(s) in conseq";
		fc_current_lhs  = estate;
		fc_prior_steps = estate.es_prior_steps;
		fc_orig_conseq  = struc_formula_of_formula (formula_of_mix_formula_with_branches rhs_p (Cperm.mkTrue pos) rhs_p_br pos) pos;
		fc_current_conseq = CF.formula_of_heap HFalse pos;
		fc_failure_pts = match r_fail_match with | Some s -> [s]| None-> [];})), prf)
  end
    (****************************************************************)  
    (* utilities for splitting the disjunctions in the antecedent and the conjunctions in the consequent *)
    (****************************************************************)  
    (* 
	   try to solve the inequalities from the rhs by making queries to the memory set:
	   - if the inequality cannot be solved -> leave it in the conseq
	   - if the equality is solved -> remove it from conseq 
    *)

and solve_ineq_debug a m c = 
  Gen.Debug.no_2 "solve_ineq "
      (Cprinter.string_of_mem_formula)
      (Cprinter.string_of_mix_formula) 
      (Cprinter.string_of_mix_formula) (fun m c -> solve_ineq a m c) m c

and solve_ineq (ante_m0:MCP.mix_formula) (memset : Cformula.mem_formula) 
      (conseq : MCP.mix_formula) : MCP.mix_formula =
  (* let memset = {mem_formula_mset = [[Cpure.SpecVar (Cpure.Prim Int, "x", Unprimed);Cpure.SpecVar (Cpure.Prim Int, "y", Unprimed)]]} in *)
  match ante_m0,conseq with
    | (MCP.MemoF at,MCP.MemoF f) ->
          begin
            (* print_endline "solve_ineq: first"; *)
            MCP.MemoF (solve_ineq_memo_formula at memset f)
          end
    | (MCP.OnePF at,MCP.OnePF f) -> 
          begin
            (* print_endline "solve_ineq: second"; *)
            MCP.OnePF (solve_ineq_pure_formula at memset f) 
          end
    |  _ ->  Error.report_error 
           {Error.error_loc = Globals.no_pos; Error.error_text = ("antecedent and consequent mismatch")}

and solve_ineq_pure_formula_debug (ante : Cpure.formula) (memset : Cformula.mem_formula) (conseq : Cpure.formula) : Cpure.formula =
  Gen.Debug.no_3 "solve_ineq_pure_formula "
      (Cprinter.string_of_pure_formula)
      (Cprinter.string_of_mem_formula) 
      (Cprinter.string_of_pure_formula) (Cprinter.string_of_pure_formula)
      (fun ante memset conseq -> solve_ineq_pure_formula ante memset conseq ) ante memset conseq

and solve_ineq_pure_formula (ante : Cpure.formula) (memset : Cformula.mem_formula) (conseq : Cpure.formula) : Cpure.formula =
  let eqset = CP.EMapSV.build_eset (MCP.pure_ptr_equations ante) in
  let rec helper (conseq : Cpure.formula) =
    match conseq with
      | Cpure.BForm (f, l) -> solve_ineq_b_formula (fun x y -> CP.EMapSV.is_equiv eqset x y) memset f
      | Cpure.And (f1, f2, pos) -> Cpure.And((helper f1), (helper f2), pos)  
      | Cpure.Or (f1, f2, l, pos) -> Cpure.Or((helper f1), (helper f2), l, pos)
            (* | Cpure.Not (f, l, pos) -> Cpure.Not((helper f), l, pos) *)
	        (* todo: think about it *)
      | _ -> conseq
	        (*| Forall of (spec_var * formula * (formula_label option) * loc)
	          | Exists of (spec_var * formula * (formula_label option) * loc)*) in
  helper conseq

and solve_ineq_memo_formula (ante : MCP.memo_pure) (memset : Cformula.mem_formula) (conseq : MCP.memo_pure) : MCP.memo_pure =
  let eqset = CP.EMapSV.build_eset (MCP.ptr_equations_aux_mp false ante) in
  let eq x y = CP.EMapSV.is_equiv eqset x y in
  let disj_eq x y = eq (fst x) (fst y) in
  let f_memo x = None in
  let f_aset x = None in
  let f_formula x = None in
  let f_b_formula e = match e with
    | CP.Neq (e1,e2,_) -> 	if (CP.is_var e1) && (CP.is_var e2) then
	    let v1 = Cpr.var_2_prop_var_top (CP.to_var e1) in
	    let v2 = Cpr.var_2_prop_var_top (CP.to_var e2) in
	    let discharge = CP.DisjSetSV.is_disj disj_eq memset.Cformula.mem_formula_mset v1 v2 in
	    let ans = (if discharge then CP.BConst(true,no_pos) else e) in 
        Some ans 
      else None
    | _ -> None in
  let f_exp x = None in
  let f = (f_memo,f_aset, f_formula, f_b_formula, f_exp) in
  MCP.transform_memo_formula f conseq

(* check whether the disjunction is of the form (x<y | y<x) which can be discharged by using the memory set *)
and check_disj ante memset l (f1 : Cpure.formula) (f2 : Cpure.formula) pos : Cpure.formula = 
  let s_ineq = solve_ineq_pure_formula ante memset in
  match f1, f2 with 
    | CP.BForm(bf1, label1), CP.BForm(bf2, label2) -> 
	      (match bf1, bf2 with
	        | CP.Lt(e1, e2, _), CP.Lt(e3, e4, _) ->
	              (match e1, e2, e3, e4 with
		            | CP.Var(sv1, _), CP.Var(sv2, _), CP.Var(sv3, _), CP.Var(sv4, _) ->
		                  if (CP.eq_spec_var sv1 sv4) && (CP.eq_spec_var sv2 sv3)
		                  then 
			                s_ineq  (CP.BForm (CP.Neq(CP.Var(sv1, pos), CP.Var(sv2, pos), pos), label1))
		                  else
			                Cpure.Or((s_ineq f1), (s_ineq f2), l, pos)
		            | _, _, _, _ -> Cpure.Or((s_ineq f1), (s_ineq f2), l, pos)
	              )
	        | _, _ -> Cpure.Or((s_ineq f1), (s_ineq f2), l, pos)
	      )
    | _, _ -> Cpure.Or((s_ineq f1), (s_ineq f2), l, pos)

and solve_ineq_b_formula_x sem_eq memset conseq : Cpure.formula =
  match conseq with
    | Cpure.Neq (e1, e2, pos) -> 
	      if (CP.is_var e1) && (CP.is_var e2) then
	        let eq x y = sem_eq (fst x) (fst y) in
	        let v1 = Cpr.var_2_prop_var_top (CP.to_var e1) in
	        let v2 = Cpr.var_2_prop_var_top (CP.to_var e2) in
	        let discharge = CP.DisjSetSV.is_disj eq memset.Cformula.mem_formula_mset v1 v2 in
	        if discharge then 
		      (* remove the diseq from the conseq *)
		      CP.mkTrue no_pos
	        else
		      (* leave the diseq as it is *)
		      CP.BForm(conseq, None) 
          else CP.BForm(conseq, None)
    | _ -> CP.BForm(conseq, None)	
	      (* todo: could actually solve more types of b_formulae *)
and solve_ineq_b_formula sem_eq memset conseq  = 
 Gen.Debug.no_2 "solve_ineq_b_formula" Cprinter.string_of_mem_formula Cprinter.string_of_b_formula Cprinter.string_of_pure_formula
  (fun _ _ -> solve_ineq_b_formula_x sem_eq memset conseq) memset conseq
(************************************* 
                                       - methods for implication discharging
***************************************)

and imply_mix_formula_new ante_m0 ante_m1 conseq_m imp_no memset 
      :bool *(Globals.formula_label option * Globals.formula_label option) list * Globals.formula_label option =
  (* let _ = print_string ("\nSolver.ml: imply_mix_formula " ^ (string_of_int !imp_no)) in *)
  let conseq_m = solve_ineq ante_m0 memset conseq_m in
  match ante_m0,ante_m1,conseq_m with
    | MCP.MemoF a, _, MCP.MemoF c -> MCP.imply_memo a c TP.imply imp_no
    | MCP.OnePF a0, MCP.OnePF a1 ,MCP.OnePF c -> 
          let increm_funct = 
            if !Globals.enable_incremental_proving then Some !TP.incremMethodsO
            else None in
          CP.imply_disj
              (TP.split_disjunctions a0) (* list with xpure0 antecedent disjunctions *)
              (TP.split_disjunctions a1) (* list with xpure1 antecedent disjunctions *)
              (TP.split_conjunctions c) (* list with consequent conjunctions *)
              TP.imply         (* imply method to be used for implication proving *)
              increm_funct
              imp_no
    | _ -> report_error no_pos ("imply_mix_formula: mix_formula mismatch")

and imply_mix_formula ante_m0 ante_m1 conseq_m imp_no memset =
  Gen.Debug.no_4 "imply_mix_formula" Cprinter.string_of_mix_formula
      Cprinter.string_of_mix_formula Cprinter.string_of_mix_formula 
      Cprinter.string_of_mem_formula
      (fun (r,_,_) -> string_of_bool r)
      (fun ante_m0 ante_m1 conseq_m memset -> imply_mix_formula_x ante_m0 ante_m1 conseq_m imp_no memset)
      ante_m0 ante_m1 conseq_m memset

and imply_mix_formula_x ante_m0 ante_m1 conseq_m imp_no memset 
      :bool *(Globals.formula_label option * Globals.formula_label option) list * Globals.formula_label option =
  let conseq_m = solve_ineq ante_m0 memset conseq_m in
  match ante_m0,ante_m1,conseq_m with
    | MCP.MemoF a, MCP.MemoF a1, MCP.MemoF c ->
          begin
            (*print_endline "imply_mix_formula: first";*)
            let r1,r2,r3 = MCP.imply_memo a c TP.imply imp_no in
            if r1 || (MCP.isConstMTrue ante_m1) then (r1,r2,r3) 
            else MCP.imply_memo a1 c TP.imply imp_no 
              (* TODO : This to be avoided if a1 is the same as a0; also pick just complex constraints *)
          end
    | MCP.OnePF a0, MCP.OnePF a1 ,MCP.OnePF c ->
          begin
            (*print_endline "imply_mix_formula first: second";*)
	        CP.imply_conj_orig 
                (TP.split_disjunctions a0) 
                (TP.split_disjunctions a1) 
                (TP.split_conjunctions c) 
	            TP.imply 
	            imp_no
          end
    | _ -> report_error no_pos ("imply_mix_formula: mix_formula mismatch")

and imply_mix_formula_no_memo_debug new_ante new_conseq imp_no imp_subno timeout memset =   
  Gen.Debug.no_3 "imply_mix_formula_no_memo" Cprinter.string_of_mix_formula Cprinter.string_of_mix_formula Cprinter.string_of_mem_formula
      (fun (r,_,_) -> string_of_bool r) 
      (fun new_ante new_conseq memset -> imply_mix_formula_no_memo new_ante new_conseq imp_no imp_subno timeout memset) 
      new_ante new_conseq memset 

and imply_mix_formula_no_memo new_ante new_conseq imp_no imp_subno timeout memset =   
  let new_conseq = solve_ineq new_ante memset new_conseq in
  let (r1,r2,r3) =  
    match timeout with
      | None -> TP.mix_imply new_ante new_conseq ((string_of_int imp_no) ^ "." ^ (string_of_int imp_subno))
      | Some t -> TP.mix_imply_timeout new_ante new_conseq ((string_of_int imp_no) ^ "." ^ (string_of_int imp_subno)) t 
  in
  Debug.devel_pprint ("IMP #" ^ (string_of_int imp_no) ^ "." ^ (string_of_int imp_subno)) no_pos;
  (r1,r2,r3)

and imply_formula_no_memo new_ante new_conseq imp_no memset =   
  let new_conseq = solve_ineq_pure_formula new_ante memset new_conseq in
  let res,_,_ = TP.imply new_ante new_conseq ((string_of_int imp_no)) false None in
  Debug.devel_pprint ("IMP #" ^ (string_of_int imp_no)) no_pos;
  res
      (*
        and return_base_cases prog ln2 rhs pos = 
      (*TODO: split this step into two steps,
        x::ls<..> & D |- (B1 \/ B2 \/ R1) * D2
        Our current changes generates (B1 or B2 or false).
        I suppose we then perform:       x::ls<..> & D |- (B1 or B2) * D2
        This may lead to some incompleteness, so I like to suggest
        we collect it as a single pure form.
        That is, we should use:          true & (B1 | B2)
        This should be done in two steps:
        x::ls<..> & D |- (B1 \/ B2)  ==> D3
        D3 |- D2 ==> D4
        The reason is to allow the instantiations to support
        further entailment.*)
        if (is_data ln2) then None
        else 
        let c2,v2,p2 = match ln2 with 
        | ViewNode {h_formula_view_name = c2; h_formula_view_arguments = v2; h_formula_view_node = p2} -> (c2, v2, p2) 
        | _ -> report_error no_pos "[solver.ml]: return_base_cases non view input\n" in
        let vd = (look_up_view_def_raw prog.prog_view_decls c2) in
        match vd.view_raw_base_case with 
	    | None  -> None 
	    | Some s ->
	    let fr_vars = (CP.SpecVar (Named vd.Cast.view_data_name, self, Unprimed)) :: vd.view_vars in			
	    let to_vars = p2 :: v2 in
	    let to_rhs = subst_avoid_capture fr_vars to_vars s in
	    let rhs = normalize_combine to_rhs rhs pos in
	    Some rhs
      (*
        and do_base_case_unfold prog ante conseq estate c1 c2 v1 v2 p1 p2 ln2 is_folding  pid pos fold_f =
        if (is_data ln2) then (None,None)
        else
        let sh_vd = vdef_fold_use_bc prog ln2 in
        let _ = Gen.Profiling.push_time "empty_predicate_testing" in
        let vd = (look_up_view_def_raw prog.prog_view_decls c1) in
        let fold_ctx = Ctx {(empty_es (mkTrueFlow ()) pos) with es_formula = ante;
        es_heap = estate.es_heap;
        es_evars = estate.es_evars;
        es_gen_expl_vars = estate.es_gen_expl_vars; 
        es_gen_impl_vars = estate.es_gen_impl_vars; 
        es_ante_evars = estate.es_ante_evars;
        es_unsat_flag = false;
        es_prior_steps = estate.es_prior_steps;
        es_path_label = estate.es_path_label;
		es_var_measures = estate.es_var_measures;
		es_var_label = estate.es_var_label} in
        let na,prf = match vd.view_base_case with
        | None ->  (CF.mkFailCtx_in(Basic_Reason ( { 
		fc_message ="failure 1 ?? when checking for aliased node";
		fc_current_lhs = estate;
		fc_prior_steps = estate.es_prior_steps;
		fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
		fc_current_conseq = conseq;
		fc_failure_pts = match pid with | Some s-> [s] | _ -> [];})), UnsatConseq)
        | Some (bc1,(base1,branches1)) -> 
	    begin
      (*let _ = print_string ("ante: "^(Cprinter.string_of_formula ante)^"\n conseq "^(Cprinter.string_of_formula conseq)^"\n") in*)
        let fr_vars = (CP.SpecVar (Named vd.Cast.view_data_name, self, Unprimed)) :: vd.view_vars in			
        let to_vars = p1 :: v1 in
      (*let _ = print_string ("from "^(Cprinter.string_of_spec_var_list fr_vars)^"\n to "^(Cprinter.string_of_spec_var_list to_vars)^"\n") in*)
        let base = MCP.subst_avoid_capture_memo fr_vars to_vars base1 in
        let branches = List.map (fun (c1,c2)-> (c1,Cpure.subst_avoid_capture fr_vars to_vars c2)) branches1 in
        let bc1 = Cpure.subst_avoid_capture fr_vars to_vars bc1 in
        let (nctx,b) = sem_imply_add prog is_folding  fold_ctx bc1 !Globals.enable_syn_base_case in
        if b then 
	  (*let _ = print_string ("successful base case guard proof \n ") in*)
		let ctx = unfold_context (prog, Some (base,branches, v1)) (SuccCtx[nctx]) p1 true pos in
		(ctx,TrueConseq)
        else  (CF.mkFailCtx_in(Basic_Reason  ( { 
		fc_message ="failure 2 ?? when checking for aliased node";
		fc_current_lhs = estate;
		fc_prior_steps = estate.es_prior_steps;
		fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
		fc_current_conseq = conseq;
		fc_failure_pts = match pid with | Some s-> [s] | _ -> [];})),TrueConseq)
        end in
        let _ = Gen.Profiling.pop_time "empty_predicate_testing" in
        if (isFailCtx na) then (None,None)
        else 
	    let cx = match na with | SuccCtx l -> List.hd l |_ -> report_error pos("do_base_case_unfold: something wrong has happened with the context") in
	    let _ = Gen.Profiling.push_time "fold_after_base_case" in
	  (*let _ = print_string ("ctx before fold: "^(Cprinter.string_of_context cx)^"\n") in*)
	    let do_fold_result,prf = fold_f sh_vd cx p2 in
	    let _ = Gen.Profiling.pop_time "fold_after_base_case" in
	  (*let _ = print_string ("after base case fold \n") in*)
	    if not(isFailCtx do_fold_result) then 
	  (*let _ = print_string "succeded in base case unfolding and then folding \n" in*)
	    (Some(do_fold_result,prf),None)
	    else                         
	    match cx with
	    | OCtx (c1,c2) ->  (None,None)
	    | Ctx c -> (None,Some c)
      *)
      *)
and do_base_case_unfold_only prog ante conseq estate anode ln2 is_folding pos rhs_b = 
  let pr x = match x with 
    | None -> "None"
    | Some _ -> "Some" in
  Gen.Debug.no_4 "do_base_case_unfold_only" 
      Cprinter.string_of_formula 
      Cprinter.string_of_formula 
      Cprinter.string_of_h_formula 
      Cprinter.string_of_h_formula 
      pr
      (fun _ _ _ _-> do_base_case_unfold_only_x prog ante conseq estate anode ln2 is_folding pos rhs_b) 
      ante conseq anode ln2

and do_base_case_unfold_only_x prog ante conseq estate lhs_node rhs_node is_folding pos rhs_b =
  if (is_data lhs_node) then None
  else begin
    (Debug.devel_pprint ("do_base_case_unfold attempt for : " ^
	    (Cprinter.string_of_h_formula lhs_node)) pos);
    let c1,v1,p1 = get_node_name lhs_node, get_node_args lhs_node , get_node_var lhs_node in
    let _ = Gen.Profiling.push_time "empty_predicate_testing" in
    let vd = (look_up_view_def_raw prog.prog_view_decls c1) in
    let fold_ctx = Ctx {(empty_es (mkTrueFlow ()) pos) with es_formula = ante;
        es_heap = estate.es_heap;
        es_evars = estate.es_evars;
        es_gen_expl_vars = estate.es_gen_expl_vars; 
        es_gen_impl_vars = estate.es_gen_impl_vars; 
        es_ante_evars = estate.es_ante_evars;
        es_unsat_flag = false;
        es_prior_steps = estate.es_prior_steps;
        es_path_label = estate.es_path_label;
		es_var_measures = estate.es_var_measures;
		es_var_label = estate.es_var_label} in
    let na,prf = match vd.view_base_case with
      | None ->  Debug.devel_pprint ("do_base_case_unfold : unsuccessful for : " ^
	        (Cprinter.string_of_h_formula lhs_node)) pos;
            (CF.mkFailCtx_in(Basic_Reason ( { 
			    fc_message ="failure 1 ?? when checking for aliased node";
			    fc_current_lhs = estate;
			    fc_prior_steps = estate.es_prior_steps;
			    fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
			    fc_current_conseq = conseq;
			    fc_failure_pts = match (get_node_label rhs_node) with | Some s-> [s] | _ -> [];})), UnsatConseq)
      | Some (bc1,(base1,branches1)) -> 
	        begin
              (*let _ = print_string ("ante: "^(Cprinter.string_of_formula ante)^"\n conseq "^(Cprinter.string_of_formula conseq)^"\n") in*)
              let fr_vars = (CP.SpecVar (Named vd.Cast.view_data_name, self, Unprimed)) :: vd.view_vars in			
              let to_vars = p1 :: v1 in
              (*let _ = print_string ("from "^(Cprinter.string_of_spec_var_list fr_vars)^"\n to "^(Cprinter.string_of_spec_var_list to_vars)^"\n") in*)
              let base = MCP.subst_avoid_capture_memo fr_vars to_vars base1 in
              let branches = List.map (fun (c1,c2)-> (c1,Cpure.subst_avoid_capture fr_vars to_vars c2)) branches1 in
              let bc1 = Cpure.subst_avoid_capture fr_vars to_vars bc1 in
              let (nctx,b) = sem_imply_add prog is_folding  fold_ctx bc1 !Globals.enable_syn_base_case in
              if b then 
		        (*let _ = print_string ("successful base case guard proof \n ") in*)
                (* TODO : need to trigger UNSAT checking here *)
		        let ctx = unfold_context_unsat_now prog (prog, Some (base,branches, v1)) (SuccCtx[nctx]) p1 pos in

		        Debug.devel_pprint ("do_base_case_unfold : successful : " ^
                    "\n Start Ante :"^(Cprinter.string_of_formula ante)^
	                "\n New Ante :"^(Cprinter.string_of_list_context_short ctx)) pos; 
                (ctx,TrueConseq)
              else begin
                Debug.devel_pprint ("do_base_case_unfold : unsuccessful for : " ^
	                (Cprinter.string_of_h_formula lhs_node)) pos; 
                (CF.mkFailCtx_in(Basic_Reason  ( { 
				    fc_message ="failure 2 ?? when checking for aliased node";
				    fc_current_lhs = estate;
				    fc_prior_steps = estate.es_prior_steps;
				    fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
				    fc_current_conseq = conseq;
				    fc_failure_pts = match (get_node_label rhs_node) with | Some s-> [s] | _ -> [];})),TrueConseq)
              end
            end in
    let _ = Gen.Profiling.pop_time "empty_predicate_testing" in
    if (isFailCtx na) then None
    else 
	  let cx = match na with | SuccCtx l -> List.hd l |_ -> report_error pos("do_base_case_unfold_only: something wrong has happened with the context") in
      let _ = Gen.Profiling.push_time "proof_after_base_case" in 
	  let do_fold_result,prf = heap_entail_one_context prog is_folding cx (CF.Base rhs_b) pos in 
	  let _ = Gen.Profiling.pop_time "proof_after_base_case" in 
      Some(do_fold_result,prf)
          (*
	        if not(isFailCtx do_fold_result) then (Some(do_fold_result,prf),None)
	        else     
	        match cx with
	        | OCtx (c1,c2) ->  (None,None)
	        | Ctx c -> (None,Some c) *)
  end
    
    
and do_match prog estate l_node r_node rhs is_folding pos : list_context *proof =
  let pr (e,_) = Cprinter.string_of_list_context e in
  let pr_h = Cprinter.string_of_h_formula in 
  Gen.Debug.no_4 "do_match" pr_h pr_h Cprinter.string_of_estate Cprinter.string_of_formula pr 
      (fun _ _ _ _ -> do_match_x prog estate l_node r_node rhs is_folding pos)
      l_node r_node estate rhs

and do_match_x prog estate l_node r_node rhs is_folding pos : list_context *proof =
  Debug.devel_pprint ("do_match: using " ^
	  (Cprinter.string_of_h_formula l_node)	^ " to prove " ^
	  (Cprinter.string_of_h_formula r_node)) pos;
    (* Debug.devel_pprint ("do_match: source LHS: "^ (Cprinter.string_of_entail_state estate)) pos; *)
    (* Debug.devel_pprint ("do_match: source RHS: "^ (Cprinter.string_of_formula rhs)) pos; *)
    let l_args, l_node_name, l_node_pr = match l_node with
      | DataNode {h_formula_data_name = l_node_name; h_formula_data_arguments = l_args; h_formula_data_perm = pr}
      | ViewNode {h_formula_view_name = l_node_name; h_formula_view_arguments = l_args; h_formula_view_perm = pr} -> (l_args, l_node_name, pr)
      | _ -> report_error no_pos "[solver.ml]: do_match non view input\n" in
    let r_args, r_node_name, r_var, r_node_pr = match r_node with
      | DataNode {h_formula_data_name = r_node_name; h_formula_data_arguments = r_args; h_formula_data_node = r_var; h_formula_data_perm = pr}
      | ViewNode {h_formula_view_name = r_node_name; h_formula_view_arguments = r_args; h_formula_view_node = r_var; h_formula_view_perm = pr} -> (r_args, r_node_name, r_var, pr) 
      | _ -> report_error no_pos "[solver.ml]: do_match non view input\n" in
    let l_h,l_p,l_fl,l_pr,l_b,l_t = split_components estate.es_formula in
    let r_h,r_p,r_fl,r_pr,r_b,r_t = split_components rhs in
    let label_list = try 
      let vdef = Cast.look_up_view_def_raw prog.prog_view_decls l_node_name in
      vdef.Cast.view_labels
    with Not_found -> List.map (fun _ -> "") l_args in
    let rho_0 = List.combine r_args l_args in (* without branch label *)
    let rho = List.combine rho_0 label_list in (* with branch label *)
    let ((impl_tvars, ivars, ivar_subs_to_conseq),other_subs) = subs_to_inst_vars rho estate.es_ivars estate.es_gen_impl_vars pos in
    let subtract = Gen.BList.difference_eq CP.eq_spec_var in
    let new_impl_vars = subtract estate.es_gen_impl_vars impl_tvars in
    let new_exist_vars = estate.es_evars(* @ivars *) in
    let new_expl_vars = estate.es_gen_expl_vars@impl_tvars in
    let new_ivars = subtract estate.es_ivars ivars in
    (* let (expl_inst, ivars', expl_vars') = (get_eqns_expl_inst rho_0 estate.es_ivars pos) in *)
    (* to_lhs only contains bindings for free vars that are not to be explicitly instantiated *)
    let (to_lhs, to_lhs_br),(to_rhs,to_rhs_br),ext_subst = 
      get_eqns_free other_subs new_exist_vars impl_tvars (* estate.es_evars *) (* estate.es_expl_vars@ *) estate.es_gen_expl_vars pos in
	
	let to_lhs_pr, to_rhs_pr, subs_pr = Cpr.get_eqns_free (l_node_pr, r_node_pr) new_exist_vars impl_tvars estate.es_gen_expl_vars pos in
			  
    (*********************************************************************)
    (* handle both explicit and implicit instantiation *)
    (* for the universal vars from universal lemmas, we use the explicit instantiation mechanism,  while, for the rest of the cases, we use implicit instantiation *)
    (* explicit instantiation is like delaying the movement of the bindings for the free vars from the RHS to the LHS *)
    (********************************************************************)
    let new_ante_p = (MCP.memoise_add_pure_N l_p to_lhs ) in
    let new_conseq_p = (MCP.memoise_add_pure_N r_p to_rhs ) in
	
	let new_l_pr = Cpr.mkAnd l_pr to_lhs_pr pos in
	let new_r_pr = Cpr.mkAnd r_pr to_rhs_pr pos in

    let new_ante = mkBase l_h new_ante_p l_t l_fl new_l_pr (CP.merge_branches l_b to_lhs_br) pos in
    let tmp_conseq = mkBase r_h new_conseq_p r_t r_fl new_r_pr (CP.merge_branches r_b to_rhs_br) pos  in
	let tmp_conseq = subst_pr_one_exp tmp_conseq subs_pr in
	
    let lhs_vars = ((CP.fv to_lhs) @(List.concat (List.map (fun (_,c)-> CP.fv c) to_lhs_br))@(Cpr.fv to_lhs_pr)) in
    (* apply the new bindings to the consequent *)
    let r_subs, l_sub = List.split (ivar_subs_to_conseq@ext_subst) in
    (*IMPORTANT TODO: global existential not took into consideration*)
    let tmp_conseq' = subst_avoid_capture r_subs l_sub tmp_conseq in

    let tmp_h2, tmp_p2, tmp_fl2, tmp_pr, tmp_b2, _ = split_components tmp_conseq' in
    let new_conseq = mkBase tmp_h2 tmp_p2 r_t r_fl tmp_pr tmp_b2 pos in
    (* only add the consumed node if the node matched on the rhs is mutable *)
    let new_consumed = 
      if not(get_imm r_node)
      then mkStarH_nn l_node estate.es_heap pos 
      else  estate.es_heap
    in
    let n_es_res,n_es_succ = match ((get_node_label l_node),(get_node_label r_node)) with
      |Some s1, Some s2 -> ((Gen.BList.remove_elem_eq (=) s1 estate.es_residue_pts),((s1,s2)::estate.es_success_pts))
      |None, Some s2 -> (estate.es_residue_pts,estate.es_success_pts)
      |Some s1, None -> ((Gen.BList.remove_elem_eq (=) s1 estate.es_residue_pts),estate.es_success_pts)
      | None, None -> (estate.es_residue_pts, estate.es_success_pts)in 
    let new_es = {estate with es_formula = new_ante;
        (* add the new vars to be explicitly instantiated *)
        (* transferring expl_vars' from gen_impl_vars,evars ==> gen_expl_vars *)
        es_gen_expl_vars = new_expl_vars (* estate.es_gen_expl_vars@expl_vars' *);
        (* update ivars - basically, those univ vars for which binsings have been found will be removed:
           for each new binding uvar = x, uvar will be removed from es_ivars and x will be added to the es_expl_vars *)
        es_gen_impl_vars = subtract new_impl_vars lhs_vars (* Gen.BList.difference_eq CP.eq_spec_var estate.es_gen_impl_vars (lhs_vars@expl_vars') *) ;
        es_evars = new_exist_vars (* Gen.BList.difference_eq CP.eq_spec_var estate.es_evars expl_vars' *) ;
        es_ivars = new_ivars (*ivars'*);
        es_heap = new_consumed;
        es_residue_pts = n_es_res;
        es_success_pts = n_es_succ; 
		(* es_subst = ((fst estate.es_subst)@r_subs, (snd estate.es_subst)@l_sub); *)
	} in
    (* let new_subst = (obtain_subst expl_inst) in *)
    (* apply the explicit instantiations to the consequent *)
    (* let new_conseq = subst_avoid_capture (fst new_subst) (snd new_subst) new_conseq in *)
    (* for each expl inst  vi = wi: make wi existential + remove vi from the exist vars *)
    let new_es' = new_es in (* {new_es with (\* es_evars = new_es.es_evars @ (snd new_subst); *\) es_must_match = false} in *)
    let new_es = pop_exists_estate ivars (* (fst new_subst) *) new_es' in
    let new_ctx = Ctx (CF.add_to_estate new_es "matching of view/node") in
    Debug.devel_pprint ("do_match (after): LHS: "^ (Cprinter.string_of_context_short new_ctx)) pos;
    Debug.devel_pprint ("do_match (after): RHS:"
	^ (Cprinter.string_of_formula new_conseq)) pos;
    let res_es1, prf1 = (*heap_entail_split_rhs_phases*) heap_entail_conjunct prog is_folding  new_ctx new_conseq pos in
    (Cformula.add_to_subst res_es1 r_subs l_sub, prf1)

and heap_entail_non_empty_rhs_heap_x prog is_folding  ctx0 estate ante conseq lhs_b rhs_b pos : (list_context * proof) =
  let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_pr,lhs_br) = CF.extr_formula_base lhs_b in
  let (rhs_h,rhs_p,rhs_t,rhs_fl,rhs_pr,rhs_br) = CF.extr_formula_base rhs_b in
  let rhs_lst = split_linear_node_guided ( CP.remove_dups_svl (h_fv lhs_h @ MCP.mfv lhs_p)) rhs_h in
  let posib_r_alias = (estate.es_evars @ estate.es_gen_impl_vars @ estate.es_gen_expl_vars) in
  let rhs_eqset = estate.es_rhs_eqset in
  let actions = Context.compute_actions prog rhs_eqset lhs_h lhs_p rhs_p posib_r_alias rhs_lst pos in
  process_action prog estate conseq lhs_b rhs_b actions is_folding pos

and heap_entail_non_empty_rhs_heap prog is_folding  ctx0 estate ante conseq lhs_b rhs_b pos : (list_context * proof) =
  Gen.Debug.loop_2_no "heap_entail_non_empty_rhs_heap" Cprinter.string_of_formula_base Cprinter.string_of_formula (fun _ -> "?") (fun _ _ -> heap_entail_non_empty_rhs_heap_x prog is_folding  ctx0 estate ante conseq lhs_b rhs_b pos) lhs_b conseq

and existential_eliminator_helper prog estate (var_to_fold:Cpure.spec_var) (c2:ident) (v2:Cpure.spec_var list) rhs_p = 
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr p = pr_pair pr_svl string_of_bool p in
  (*let t (r,_) = not(Gen.BList.list_equiv_eq CP.eq_spec_var (var_to_fold::v2) r) in*)
  Gen.Debug.no_3(*_opt t*) "existential_eliminator_helper" Cprinter.string_of_spec_var pr_id Cprinter.string_of_spec_var_list pr 
      (fun _ _ _ -> existential_eliminator_helper_x prog estate (var_to_fold:Cpure.spec_var) (c2:ident) (v2:Cpure.spec_var list) rhs_p) var_to_fold c2 v2

(* this helper does not seem to eliminate anything *)
and existential_eliminator_helper_x prog estate (var_to_fold:Cpure.spec_var) (c2:ident) (v2:Cpure.spec_var list) rhs_p = 
  let comparator v1 v2 = (String.compare (Cpure.name_of_spec_var v1) (Cpure.name_of_spec_var v2))==0 in
  let pure = rhs_p in
  let ptr_eq = MCP.ptr_equations_with_null pure in
  let ptr_eq = (List.map (fun c->(c,c)) v2) @ ptr_eq in
  let asets = MCP.alias_nth 9 ptr_eq in
  try
	let vdef = look_up_view_def_raw prog.Cast.prog_view_decls c2 in
	let subs_vars = List.combine vdef.view_vars v2 in
	let sf = (CP.SpecVar (Named vdef.Cast.view_data_name, self, Unprimed)) in
	let subs_vars = (sf,var_to_fold)::subs_vars in
	((List.map (fun (c1,c2)-> 
		if (List.exists (comparator c1) vdef.view_case_vars) then
		  if (List.exists (comparator c2) estate.es_evars) then
			let paset = MCP.get_aset asets c2 in
			List.find (fun c -> not (List.exists (comparator c) estate.es_evars )) paset 
		  else c2
		else c2					
	) subs_vars),true)
  with | Not_found -> (var_to_fold::v2,false) 

and do_fold_w_ctx fold_ctx prog estate conseq rhs_node vd rhs_rest rhs_b is_folding pos = 
  let pr2 x = match x with
    | None -> "None"
    | Some f -> Cprinter.string_of_struc_formula f.view_formula in
  let pr (x,_) = Cprinter.string_of_list_context x in
  Gen.Debug.loop_3_no  "do_fold_w_ctx" Cprinter.string_of_context Cprinter.string_of_h_formula pr2 pr
      (fun _ _ _ -> do_fold_w_ctx_x fold_ctx prog estate conseq rhs_node vd rhs_rest rhs_b is_folding pos) 
      fold_ctx rhs_node vd
      (*
        ln2 = p2 (node) c2 (name) v2 (arguments) r_rem_brs (remaining branches) r_p_cond (pruning conditions) pos2 (pos)
        resth2 = rhs_h - ln2
        ctx0?
        is_folding?
      *)
and do_fold_w_ctx_x fold_ctx prog estate conseq ln2 vd resth2 rhs_b is_folding pos = 
  let var_to_fold = get_node_var ln2 in
  let ctx0 = Ctx estate in
  let (rhs_h, rhs_p, rhs_t, rhs_fl, rhs_pr, rhs_br) = CF.extr_formula_base rhs_b in
  let (p2,c2,v2,pid,r_rem_brs,r_p_cond,r_perm,pos2) = 
    match ln2 with
      | DataNode ({ h_formula_data_node = p2;
        h_formula_data_name = c2;
        h_formula_data_imm = imm2;
		h_formula_data_perm = r_perm;
        h_formula_data_arguments = v2;
        h_formula_data_label = pid;
        h_formula_data_remaining_branches =r_rem_brs;
        h_formula_data_pruning_conditions = r_p_cond;
        h_formula_data_pos = pos2})
      | ViewNode ({ h_formula_view_node = p2;
        h_formula_view_name = c2;
		h_formula_view_perm = r_perm;
        h_formula_view_imm = imm2;
        h_formula_view_arguments = v2;
        h_formula_view_label = pid;
        h_formula_view_remaining_branches = r_rem_brs;
        h_formula_view_pruning_conditions = r_p_cond;
        h_formula_view_pos = pos2}) -> (p2,c2,v2,pid,r_rem_brs,r_p_cond,r_perm,pos2)
      | _ -> report_error no_pos ("do_fold_w_ctx: data/view expected but instead ln2 is "^(Cprinter.string_of_h_formula ln2) ) in
  (* let _ = print_string("in do_fold\n") in *) 
  let r_perm_f = Cpr.solve_on rhs_pr r_perm in
  let original2 = if (is_view ln2) then (get_view_original ln2) else true in
  let unfold_num = (get_view_unfold_num ln2) in
  let estate = estate_of_context fold_ctx pos2 in
  let (new_v2,use_case) = existential_eliminator_helper prog estate (var_to_fold:Cpure.spec_var) (c2:ident) (v2:Cpure.spec_var list) rhs_p in

  let view_to_fold = ViewNode ({  
	  h_formula_view_node = List.hd new_v2 (*var_to_fold*);
	  h_formula_view_name = c2;
	  h_formula_view_perm = r_perm;
	  h_formula_view_imm = get_view_imm ln2;
      h_formula_view_original = original2;
      h_formula_view_unfold_num = unfold_num;
	  h_formula_view_arguments = List.tl new_v2;
	  h_formula_view_modes = get_view_modes ln2;
	  h_formula_view_coercible = true;
	  h_formula_view_origins = get_view_origins ln2;
	  h_formula_view_label = pid;           (*TODO: the other alternative is to use none*)
	  h_formula_view_remaining_branches = r_rem_brs;
	  h_formula_view_pruning_conditions = r_p_cond;
	  h_formula_view_pos = pos2}) in
  let fold_rs, fold_prf = fold_op prog fold_ctx view_to_fold vd (* false *) r_perm_f use_case pos in
  if not (CF.isFailCtx fold_rs) then
	let b = { formula_base_heap = resth2;
	formula_base_pure = rhs_p;
	formula_base_type = rhs_t;
	formula_base_perm = rhs_pr;
	(* formula_base_imm = contains_immutable_h_formula resth2; *)
	formula_base_branches = rhs_br;
	formula_base_flow = rhs_fl;		
	formula_base_label = None;   
	formula_base_pos = pos } in
	let tmp, tmp_prf = process_fold_result prog is_folding estate fold_rs p2 v2 b pos in
	let prf = mkFold ctx0 conseq p2 fold_prf tmp_prf in
	(tmp, prf)
  else begin
	Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: unable to fold:\n"
	^ (Cprinter.string_of_context ctx0) ^ "\n"
	^ "to:ln2: "
	^ (Cprinter.string_of_h_formula ln2)
	^ "\nrhs_p: "
	^ (Cprinter.string_of_mix_formula rhs_p) ^"..end") pos;
	(fold_rs, fold_prf)
  end 

and  combine_results ((res_es1,prf1): list_context * Prooftracer.proof) 
      ((res_es2,prf2): list_context * Prooftracer.proof) : list_context * Prooftracer.proof =
  let prf = Search [prf1; prf2] in
  let res = (fold_context_left [res_es1;res_es2]) in
  (* this is a union *)
  (*let _ = print_string ("\nmatch "^(string_of_bool(isFailCtx res_es1))^
	"\n coerc: "^(string_of_bool(isFailCtx res_es2))^"\n result :"^
	(string_of_bool(isFailCtx res_es1))^"\n") in*)
  let prf = match isFailCtx res_es1, isFailCtx res_es2 with
    | true,true -> prf
	| true,false -> prf2
	| false ,true -> prf1
	| false , false -> prf in
  (res,prf)
      
      
and do_fold prog vd estate conseq rhs_node rhs_rest rhs_b is_folding pos =
  let fold_ctx = Ctx {(empty_es (mkTrueFlow () ) pos) with 
	  es_formula = estate.es_formula;
	  es_heap = estate.es_heap;
	  es_evars = estate.es_evars;
	  es_gen_expl_vars = estate.es_gen_expl_vars; 
	  es_gen_impl_vars = estate.es_gen_impl_vars; 
	  es_ante_evars = estate.es_ante_evars;
	  es_pure = estate.es_pure;
	  es_unsat_flag  = false;
	  es_success_pts = estate.es_success_pts;
	  es_residue_pts = estate.es_residue_pts;
	  es_id  = estate.es_id;
	  es_orig_ante  = estate.es_orig_ante;
	  es_orig_conseq = estate.es_orig_conseq;
	  es_prior_steps = estate.es_prior_steps;
      es_path_label = estate.es_path_label;
	  es_var_measures = estate.es_var_measures;
	  es_var_label = estate.es_var_label} in
  do_fold_w_ctx fold_ctx prog estate conseq rhs_node vd rhs_rest rhs_b is_folding pos
      
      
and do_base_fold prog estate conseq rhs_node rhs_rest rhs_b is_folding pos=
  let vd = (vdef_fold_use_bc prog rhs_node) in
  if (vd==None) then   (CF.mkFailCtx_in (Basic_Reason (mkFailContext "No base-case for folding" estate (CF.formula_of_heap HFalse pos) None pos)), NoAlias)
  else do_fold prog vd estate conseq rhs_node rhs_rest rhs_b is_folding pos

and do_full_fold_x prog estate conseq rhs_node rhs_rest rhs_b is_folding pos = 
  do_fold prog None estate conseq rhs_node rhs_rest rhs_b is_folding pos

and do_full_fold prog estate conseq rhs_node rhs_rest rhs_b is_folding pos =
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 x = Cprinter.string_of_list_context_short (fst x) in
  let pr3 =fun b-> Cprinter.string_of_formula (CF.Base b) in
  let pr4 = Cprinter.string_of_estate in
  Gen.Debug.no_3 "do_full_fold" pr1 pr3 pr4 pr2 
      (fun _ _ _-> do_full_fold_x prog estate conseq rhs_node rhs_rest rhs_b is_folding pos) rhs_node rhs_b estate
      

and push_hole_action_x a1 r1=
  match Context.action_get_holes a1 with
    | None -> r1
    | Some h -> Context.push_crt_holes_list_ctx r1 h
and push_hole_action a1 r1=
  Gen.Debug.loop_1_no "push_hole_action" pr_no pr_no 
      (fun _ -> push_hole_action_x a1 r1) a1


and advance_unfold_struc prog (ctx:context) (conseq:struc_formula) : (Context.action_wt) list =
  let get_disj_ext_formula f = match f with
    | EBase e -> CF.split_conjuncts e.formula_ext_base 
    | _ -> [] in
  let get_disj_struc sf = List.concat (List.map (get_disj_ext_formula) conseq) in
  let ls = get_disj_struc conseq in
  advance_unfold prog ctx ls 

and advance_unfold prog (ctx:context) (conseq:formula list) : (Context.action_wt) list =
  let pr1 = Cprinter.string_of_context_short in
  let pr2 = pr_list (Context.string_of_action_wt_res)  in
  let p0 fl = (string_of_int (List.length fl)) ^ (pr_list Cprinter.string_of_formula fl) in
  Gen.Debug.no_2 "advance_unfold" pr1 p0 pr2 (fun _ _ -> advance_unfold_x prog ctx conseq) ctx conseq 

and advance_unfold_x prog (ctx:context) (conseq:formula list) : (Context.action_wt) list =
  (* let rec get_disj (c:formula) = match c with *)
  (*   | Or e -> (get_disj e.formula_or_f1)@(get_disj e.formula_or_f2) *)
  (*   | _ -> [c] in *)
  let r = (* CF.split_conjuncts *)conseq in
  if (List.length r)<=1 then []
  else 
    match ctx with
      | OCtx _ ->  Error.report_error { Error.error_loc = no_pos;
		Error.error_text = "advance_unfold : OCtx unexpected" }
      | Ctx es ->
            let a = List.map (comp_act prog es) r in
            let a = List.map Context.pick_unfold_only a in
            let _ = List.filter (fun x -> not(x==[])) a in
            if a==[] then []
            else List.concat a

and comp_act prog (estate:entail_state) (rhs:formula) : (Context.action_wt) =
  let pr1 es = Cprinter.string_of_formula es.es_formula in
  let pr2 = Cprinter.string_of_formula in
  let pr3 = Context.string_of_action_wt_res in
  Gen.Debug.no_2 "comp_act" pr1 pr2 pr3 (fun _ _ -> comp_act_x prog estate rhs) estate rhs

and comp_act_x prog (estate:entail_state) (rhs:formula) : (Context.action_wt) =
  let rhs_b = extr_rhs_b rhs in
  let lhs_b = extr_lhs_b estate in
  let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_pr,lhs_br) = extr_formula_base lhs_b in
  let (rhs_h,rhs_p,rhs_t,rhs_fl,rhs_pr,rhs_br) = extr_formula_base rhs_b in
  let rhs_lst = split_linear_node_guided ( CP.remove_dups_svl (h_fv lhs_h @ MCP.mfv lhs_p)) rhs_h in
  (* let rhs_lst = [] in *)
  let posib_r_alias = (estate.es_evars @ estate.es_gen_impl_vars @ estate.es_gen_expl_vars) in
  let rhs_eqset = estate.es_rhs_eqset in
   (0,Context.compute_actions prog rhs_eqset lhs_h lhs_p rhs_p posib_r_alias rhs_lst no_pos)

and process_unfold prog estate conseq a is_folding pos has_post pid =
  match a with
    | Context.M_unfold ({Context.match_res_lhs_node=lhs_node},unfold_num) ->
          let lhs_var = get_node_var lhs_node in
            let delta1 = unfold_nth 1 (prog,None) estate.es_formula lhs_var true unfold_num pos in (* update unfold_num *)
            let ctx1 = build_context (Ctx estate) delta1 pos in
			let ctx1 = set_unsat_flag ctx1 true in
			let res_rs, prf1 = heap_entail_one_context_struc_x prog is_folding has_post ctx1 conseq pos pid in
			let prf = mkUnfold_no_conseq (Ctx estate) lhs_node prf1 in
			(res_rs, prf)
    | _ -> report_error no_pos ("process_unfold - expecting just unfold operation")
      
and process_action_x prog estate conseq lhs_b rhs_b a is_folding pos = 
  let r1,r2 = match a with
    | Context.M_match {
          Context.match_res_lhs_node = lhs_node;
          Context.match_res_lhs_rest = lhs_rest;
          Context.match_res_rhs_node = rhs_node;
          Context.match_res_rhs_rest = rhs_rest;} ->
          let subsumes, to_be_proven = prune_branches_subsume(*_debug*) prog lhs_node rhs_node in
		  if not subsumes then  (CF.mkFailCtx_in (Basic_Reason (mkFailContext "there is a mismatch in branches " estate conseq (get_node_label rhs_node) pos)), NoAlias)
          else
            let new_estate = {estate with es_formula = Base{lhs_b with formula_base_heap = lhs_rest}} in
			(*TODO: if prunning fails then try unsat on each of the unprunned branches with respect to the context,
			  if it succeeds and the flag from to_be_proven is true then make current context false*)
            let rhs_p = match to_be_proven with
              | None -> rhs_b.formula_base_pure
              | Some (p,_) -> MCP.memoise_add_pure rhs_b.formula_base_pure p in
            let n_rhs_b = Base {rhs_b with formula_base_heap = rhs_rest;formula_base_pure = rhs_p} in
            let res_es0, prf0 = do_match prog new_estate lhs_node rhs_node n_rhs_b is_folding pos in
            (res_es0,prf0)
			
	 | Context.M_split_match {
          Context.match_res_lhs_node = lhs_node;
          Context.match_res_lhs_rest = lhs_rest;
          Context.match_res_rhs_node = rhs_node;
          Context.match_res_rhs_rest = rhs_rest;} ->
			let v_rest, v_consumed = Cpr.fresh_perm_var () , Cpr.fresh_perm_var () in
			let n_lhs_perm,_,b = Cpr.comp_perm_split true v_rest v_consumed lhs_b.formula_base_perm rhs_b.formula_base_perm (get_node_perm lhs_node) (get_node_perm rhs_node) in
			if b<=0 then 
				(CF.mkFailCtx_in (Basic_Reason (mkFailContext "lhs has lower permissions than required or rhs is false" estate conseq (get_node_label rhs_node) pos)), NoAlias)
			else
        let subsumes, to_be_proven = prune_branches_subsume(*_debug*) prog lhs_node rhs_node in
        if not subsumes then  (CF.mkFailCtx_in (Basic_Reason (mkFailContext "there is a mismatch in branches " estate conseq (get_node_label rhs_node) pos)), NoAlias)
        else

			let n_lhs_h = mkStarH_nn lhs_rest (set_perm_node (Some v_rest) lhs_node) pos in				
			let new_estate = {estate with 
								es_formula = Base{ lhs_b with formula_base_heap = n_lhs_h; formula_base_perm = n_lhs_perm }; 
								es_ante_evars = [v_rest;v_consumed]@estate.es_ante_evars } in
			(*TODO: if prunning fails then try unsat on each of the unprunned branches with respect to the context,
			  if it succeeds and the flag from to_be_proven is true then make current context false*)
            let rhs_p = match to_be_proven with
              | None -> rhs_b.formula_base_pure
              | Some (p,_) -> MCP.memoise_add_pure rhs_b.formula_base_pure p in
            let n_rhs_b = Base {rhs_b with formula_base_heap = rhs_rest;formula_base_pure = rhs_p} in
			let n_lhs_node = set_perm_node (Some v_consumed) lhs_node in
            let res_es0, prf0 = do_match prog new_estate n_lhs_node rhs_node n_rhs_b is_folding pos in
            (res_es0,prf0)
| Context.M_r_split_match {
          Context.match_res_lhs_node = lhs_node;
          Context.match_res_lhs_rest = lhs_rest;
          Context.match_res_rhs_node = rhs_node;
          Context.match_res_rhs_rest = rhs_rest;} ->
			let v_rest, v_consumed = Cpr.fresh_perm_var () , Cpr.fresh_perm_var () in
			let l_p,r_f,b = Cpr.comp_perm_split false v_rest v_consumed lhs_b.formula_base_perm rhs_b.formula_base_perm (get_node_perm lhs_node) (get_node_perm rhs_node) in
			if b>=0 then 
				(CF.mkFailCtx_in (Basic_Reason (mkFailContext "rhs has lower permissions than required or rhs is false" estate conseq (get_node_label rhs_node) pos)), NoAlias)
			else
        let subsumes, to_be_proven = prune_branches_subsume(*_debug*) prog lhs_node rhs_node in
        if not subsumes then  (CF.mkFailCtx_in (Basic_Reason (mkFailContext "there is a mismatch in branches " estate conseq (get_node_label rhs_node) pos)), NoAlias)
        else

			let n_rhs_h = mkStarH_nn rhs_rest (set_perm_h (Some v_rest) rhs_node) pos in	
      let comp_vars v_r v_c r_p evs impl expl =
        match r_p with
          | [] -> (v_r::v_c::evs, impl, expl, l_p, Cpr.mkAnd rhs_b.formula_base_perm r_f no_pos)
          | v::_ -> 
            let nevs = if (Gen.BList.mem_eq CP.eq_spec_var v evs) then v_r::v_c::evs else evs in
            if (Gen.BList.mem_eq CP.eq_spec_var v expl) then  
              (nevs, impl, v_r::v_c::expl, l_p, Cpr.mkAnd rhs_b.formula_base_perm r_f no_pos)
            else if (Gen.BList.mem_eq CP.eq_spec_var v impl) then  
              (nevs, v_r::v_c::impl, expl, Cpr.mkAnd l_p r_f no_pos, rhs_b.formula_base_perm)
            else (nevs, impl, expl, l_p, Cpr.mkAnd rhs_b.formula_base_perm r_f no_pos)  in
      let evars, impl, expl,l_p,r_p = comp_vars v_rest v_consumed (get_node_perm rhs_node) estate.es_evars estate.es_gen_impl_vars estate.es_gen_expl_vars in 
			let new_estate = {estate with 
								es_formula = Base{ lhs_b with formula_base_heap = lhs_rest; formula_base_perm = l_p }; 
								es_evars = evars;
                es_gen_impl_vars = impl; 
                es_gen_expl_vars = expl; (*[v_rest;v_consumed]@estate.es_evars;*)} in
			(*TODO: if prunning fails then try unsat on each of the unprunned branches with respect to the context,
			  if it succeeds and the flag from to_be_proven is true then make current context false*)
            let rhs_p = match to_be_proven with
              | None -> rhs_b.formula_base_pure
              | Some (p,_) -> MCP.memoise_add_pure rhs_b.formula_base_pure p in
            let n_rhs_b = Base {rhs_b with formula_base_heap = n_rhs_h;formula_base_pure = rhs_p; formula_base_perm = r_p} in
            let n_rhs_node = set_perm_h (Some v_consumed) rhs_node in
            let res_es0, prf0 = do_match prog new_estate lhs_node n_rhs_node n_rhs_b is_folding pos in
            (res_es0,prf0)
            
    | Context.M_fold {
          Context.match_res_rhs_node = rhs_node;
          Context.match_res_rhs_rest = rhs_rest;} -> 
          do_full_fold prog estate conseq rhs_node rhs_rest rhs_b is_folding pos
              
    | Context.M_unfold ({Context.match_res_lhs_node=lhs_node},unfold_num) -> 
          let lhs_var = get_node_var lhs_node in
          let curr_unfold_num = (get_view_unfold_num lhs_node)+unfold_num in
          if (curr_unfold_num>1) then 
            (CF.mkFailCtx_in(Basic_Reason(mkFailContext "ensuring finite unfold" estate conseq (get_node_label lhs_node) pos)),NoAlias)
          else
            let delta1 = unfold_nth 1 (prog,None) estate.es_formula lhs_var true unfold_num pos in (* update unfold_num *)
            let ctx1 = build_context (Ctx estate) delta1 pos in
			let ctx1 = set_unsat_flag ctx1 true in
			let res_rs, prf1 = heap_entail_one_context prog is_folding ctx1 conseq pos in
			let prf = mkUnfold (Ctx estate) conseq lhs_node prf1 in
			(res_rs, prf)
    | Context.M_base_case_unfold {
          Context.match_res_lhs_node = lhs_node;
          Context.match_res_rhs_node = rhs_node;}->
          let ans = do_base_case_unfold_only prog estate.es_formula conseq estate lhs_node rhs_node is_folding pos rhs_b in
          (match ans with
            | None -> (CF.mkFailCtx_in(Basic_Reason(mkFailContext "base_case_unfold failed" estate conseq (get_node_label rhs_node) pos)),NoAlias)
            | Some x -> x)
    | Context.M_base_case_fold {
          Context.match_res_rhs_node = rhs_node;
          Context.match_res_rhs_rest = rhs_rest;} ->
          if (estate.es_cont != []) then (CF.mkFailCtx_in (Continuation (mkFailContext "try the continuation" estate (Base rhs_b) (get_node_label rhs_node) pos)), NoAlias)
		  else do_base_fold prog estate conseq rhs_node rhs_rest rhs_b is_folding pos
    | Context.M_rd_lemma {
          Context.match_res_lhs_node = lhs_node;
          Context.match_res_lhs_rest = lhs_rest;
          Context.match_res_rhs_node = rhs_node;
          Context.match_res_rhs_rest = rhs_rest;
      } -> 
          (* let _ = print_string ("!!! do_coercion should try directly right lemmas ") in *)
          let r1,r2 = do_coercion prog None estate conseq lhs_rest rhs_rest lhs_node lhs_b rhs_b rhs_node is_folding pos in
          (r1,Search r2)
    | Context.M_lemma  ({
          Context.match_res_lhs_node = lhs_node;
          Context.match_res_lhs_rest = lhs_rest;
          Context.match_res_rhs_node = rhs_node;
          Context.match_res_rhs_rest = rhs_rest;
      },ln) ->
          let _ = match ln with
            | None -> () 
            | Some c -> print_string ("!!! do_coercion should try directly lemma: "^c.coercion_name^"\n") in
          let r1,r2 = do_coercion prog ln estate conseq lhs_rest rhs_rest lhs_node lhs_b rhs_b rhs_node is_folding pos in
          (r1,Search r2)
    | Context.Undefined_action mr -> (CF.mkFailCtx_in (Basic_Reason (mkFailContext "undefined action" estate (Base rhs_b) None pos)), NoAlias)
    | Context.M_Nothing_to_do s -> (CF.mkFailCtx_in (Basic_Reason (mkFailContext s estate (Base rhs_b) None pos)), NoAlias)
    | Context.Seq_action l -> 
          (CF.mkFailCtx_in (Basic_Reason (mkFailContext "undefined action" estate (Base rhs_b) None pos)), NoAlias)
    | Context.Search_action l ->
          let r = List.map (fun (_,a1) -> process_action_x prog estate conseq lhs_b rhs_b a1 is_folding pos) l in
          List.fold_left combine_results (List.hd r) (List.tl r) in
  if (Context.is_complex_action a) then (r1,r2) else 
    (push_hole_action a r1,r2)
        
and process_action prog estate conseq lhs_b rhs_b a is_folding pos =
  let pr1 = Context.string_of_action_res in
  let pr2 x = Cprinter.string_of_list_context_short (fst x) in
  Gen.Debug.loop_1_no "process_action" pr1 pr2 (fun _ -> process_action_x prog estate conseq lhs_b rhs_b a is_folding pos) a
      
      
(************************* match_all_nodes ******************)
(* 
   match ln2 with
   | DataNode ({ h_formula_data_node = p2;
   h_formula_data_name = c2;
   h_formula_data_imm = imm2;
   h_formula_data_arguments = v2;
   h_formula_data_label = pid;
   h_formula_data_remaining_branches =r_rem_brs;
   h_formula_data_pruning_conditions = r_p_cond;
   h_formula_data_pos = pos2})
   | ViewNode ({ h_formula_view_node = p2;
   h_formula_view_name = c2;
   h_formula_view_imm = imm2;
   h_formula_view_arguments = v2;
   h_formula_view_label = pid;
   h_formula_view_remaining_branches = r_rem_brs;
   h_formula_view_pruning_conditions = r_p_cond;
   h_formula_view_pos = pos2}) -> begin
   Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: trying to prove " ^ (Cprinter.string_of_h_formula ln2)) pos;
   

   match actions with 
   | Failed -> 
(* let _ = print_string("Matching result: Failed -> setting continuation to " ^ (Cprinter.string_of_formula (Base(rhs_b))) ^ "\n") in *)

   (CF.mkFailCtx_in (Continuation ( {
   fc_message = "failed 1 ?? to find a match";
   fc_current_lhs = estate;
   fc_prior_steps = estate.es_prior_steps;
   fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
   fc_current_conseq = Base(rhs_b);
   fc_failure_pts = match pid with | Some s-> [s] | _ -> [];})), NoAlias) (* p2 is not mentioned in LHS, failure *)
   | NoMatch -> begin (* p2 is mentioned in LHS, but no matching node/predicate is found *)
(* let _ = print_string("no match\n") in *)
   if is_data ln2 then begin (* fail *)
(* let _ = print_string("Matching result: NoMatch -> setting continuation to " ^ (Cprinter.string_of_formula (Base(rhs_b))) ^ "\n") in *)
   Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: no aliased node for data node " ^ (Cprinter.string_of_h_formula ln2)^ " is found in LHS\n") pos;
   (CF.mkFailCtx_in (Continuation ( {
   fc_message = "failed to find a match in conseq for "^Cprinter.string_of_h_formula(ln2);
   fc_current_lhs = estate;
   fc_prior_steps = estate.es_prior_steps;
   fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
   fc_current_conseq = Base(rhs_b);
   fc_failure_pts = match pid with | Some s-> [s] | _ -> [];})), NoAlias) 
   end
   else
(* there is a continuation to try *)
   if (estate.es_cont != []) then
(* let _ = print_string("try the cont!!!\n\n") in *)
   (CF.mkFailCtx_in (Continuation ( {
   fc_message = "try the continuation";
   fc_current_lhs = estate;
   fc_prior_steps = estate.es_prior_steps;
   fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
   fc_current_conseq = Base(rhs_b);
   fc_failure_pts = match pid with | Some s-> [s] | _ -> [];})), NoAlias)     
   else
(* there is no continuation to try *)
   begin (* attempting to fold against the base case *)
   Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: folding with no node on lhs: " ^ (Cprinter.string_of_spec_var p2)
   ^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx0) ^ "\nln2:\n" ^ (Cprinter.string_of_h_formula ln2) ^ "\nrhs_p:\n" ^ (Cprinter.string_of_mix_formula rhs_p)) pos;
   do_base_fold p2 ln2 (* p2 is mentioned in LHS, p2 can be fold target var_to_fold *)
   end (* end of emty anodes case *)
   end
   | Match (matches) -> begin
(* one or more aliased nodes are found, try all of them one by one. *)
(* When trying a node, add the remaining back to resth1. *)
(****************************************************************************************************************************)
(* start of check_aliased_node *)
(*****************************************************************************************************************************)
(* let rec check_aliased_node_debug (a,r) resth1 =  *)
(* Gen.Debug.no_2 "check_aliased_node" *)
(*   (fun (x, y) -> Cprinter.string_of_h_formula x) *)
(*   (Cprinter.string_of_h_formula) *)
(*   (fun (x,y) -> Cprinter.string_of_list_context x) *)
(*   check_aliased_node *)
(*   (a,r) resth1 *)
   let rec check_aliased_node (anode, r_flag) resth1 act: (list_context * proof) =
   match anode with 
   | ViewNode ({ h_formula_view_node = p1;
   h_formula_view_name = c1;
   h_formula_view_arguments = v1;
   h_formula_view_pos = pos1})
   | DataNode ({ h_formula_data_node = p1;
   h_formula_data_name = c1;
   h_formula_data_arguments = v1;
   h_formula_data_pos = pos1}) ->
   if r_flag = Context.Root then begin (* matching occurs at root *)
   if c1 = c2 then 

(* try and make sure the branches match, if not and if some conditions
   can be used to prune the necesary branch then add those conditions to the right
   and do the prune*)
   let subsumes, to_be_proven = prune_branches_subsume(*_debug*) prog anode ln2 in
   if not subsumes then  
   (CF.mkFailCtx_in (Basic_Reason ({
   fc_message = "there is a mismatch in branches ";
   fc_current_lhs = estate;
   fc_prior_steps = estate.es_prior_steps;
   fc_orig_conseq = estate.es_orig_conseq;
   fc_current_conseq = CF.formula_of_heap HFalse pos;
   fc_failure_pts =match pid with | Some s-> [s] | _ -> [];})), NoAlias)
   else
   (  
   let rhs_p,rhs_b = 
   match to_be_proven with
   | None -> rhs_p,rhs_b
   | Some p -> 
   let np = MCP.memoise_add_pure rhs_p p in
   (np,{rhs_b with formula_base_pure = rhs_p}) in
   let ans = do_base_case_unfold_only prog ante conseq estate c1 v1 p1 anode ln2 is_folding pid pos rhs_b in
(*should use def version as it is always folding against base case
   probably considerable speed gain*) 
   match ans with 
   | Some x -> x  (* direct unfold and continue *)
   | None ->  
   let new_estate = {estate with es_formula = (mkBase resth1 lhs_p lhs_t lhs_fl lhs_br pos)} in
   let res_es0, prf0 = do_match prog new_estate v1 v2 c1 c2 anode ln2 
   (mkBase resth2 rhs_p rhs_t rhs_fl rhs_br pos) is_folding  p2 pos in
   let res_es1, prf1 = 
   if (!Globals.exhaust_match) then 
   let n_rhs = return_base_cases prog c2 v2 p2 ln2 (mkBase resth2 rhs_p rhs_t rhs_fl rhs_br pos) pos in
   match n_rhs with
   | None -> (res_es0,prf0)
   | Some s ->
(* let _ = print_string ("\n now entailing \n") in  *)
   let new_estate2 = impl_to_expl estate v2 in                            
   let res_es2, prf2 = heap_entail_conjunct prog is_folding  (Ctx new_estate2) s pos in
(*TODO: move back the explicits as implicits after this heap_entail*)
(* let res_es2 = transform_list_context_expl_to_impl p2 v2 in*)
   (list_context_union res_es2 res_es0, Prooftracer.Unknown)
   else (res_es0,prf0) in
   let res_es1, prf1 = 
   if (* false *) (is_view ln2)  then  combine_results (res_es1,prf1) (do_base_fold p2 ln2)
   else (res_es1,prf1) in
(* let copy_enable_distribution = !enable_distribution in *)
(*******************************************************************************************************************************************************************************************)
(* call to do_coercion *)
(* try coercion as well *)
(*******************************************************************************************************************************************************************************************)
   let ans =	
   if (is_view anode) || (is_view ln2) then
   (Debug.devel_pprint ("do_coercion for LHS:" ^ (Cprinter.string_of_h_formula anode) ^" RHS:"^(Cprinter.string_of_h_formula ln2)^ "\n") pos;
   Some (do_coercion c1 c2 prog estate conseq ctx0 resth1 resth2 anode lhs_b rhs_b ln2 is_folding pos pid)  )
(* else (CF.SuccCtx [], []) in
   - this does not work! *)
   else None in
   match ans with
   | None -> (res_es1, Search [prf1])
   | Some (res_es2,prf2) -> begin
(* enable_distribution := copy_enable_distribution; *)
   let prf1 = mkMatch ctx0 conseq ln2 [prf1] in
   combine_results (res_es1,prf1) (res_es2,(Search prf2))
(*moved to combine results let prf = match isFailCtx res_es1, isFailCtx res_es2 with | false ,true -> enable_distribution := true; prf1 in (res,prf)*)
   end
   )
   else (* c1 not equal c2  *)
   begin
   if is_view ln2 && is_data anode then 
   begin (* fold *)
   Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: folding: "
   ^ (Cprinter.string_of_spec_var p2)
   ^ "\nante:\n"
   ^ (Cprinter.string_of_formula ante)
   ^ "\nln2:\n"
   ^ (Cprinter.string_of_h_formula ln2)
   ^ "\nrhs_p:\n"
   ^ (Cprinter.string_of_mix_formula rhs_p)) pos;
   do_full_fold p2 
   end else if is_data ln2 && is_view anode then 
   begin (* unfold *)
(* TODO : ADD dd debug message for unfolding *)
   let delta1 = unfold_nth 1 (prog,None) ante p1 true pos in
   let ctx1 = build_context ctx0 delta1 pos in
   let ctx1 = set_unsat_flag ctx1 true in
   let res_rs, prf1 = heap_entail_one_context prog is_folding  ctx1 conseq pos in
   let prf = mkUnfold ctx0 conseq anode prf1 in
   (res_rs, prf)
   end else 
(* TODO : ADD dd debug message base-unfolding; indicates when it fails after folding! *)
   let ans = do_base_case_unfold_only prog ante conseq estate c1 v1 p1 anode ln2 is_folding  pid pos rhs_b in
   match ans with 
   | Some x -> x
   | None ->                          
   if !Globals.use_coercion then 
   begin
(* two different predicates match, try coercion *)
   Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: " ^ "trying coercion") pos;
   let res, prfs = do_coercion c1 c2 prog estate conseq ctx0 resth1 resth2 anode (*lhs_p lhs_t lhs_fl lhs_br rhs_p rhs_t rhs_fl*) lhs_b rhs_b ln2 is_folding pos pid in
   let prf = mkCoercion2 ctx0 conseq prfs in
   (res, prf)
   end else 
   begin
   Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: " ^ "can't reduce, fold, unfold") pos;
   (CF.mkFailCtx_in (Basic_Reason ( {
   fc_message = "can't reduce, fold, unfold";
   fc_current_lhs = estate;
   fc_prior_steps = estate.es_prior_steps;
   fc_orig_conseq = estate.es_orig_conseq;
   fc_current_conseq = CF.formula_of_heap HFalse pos;
   fc_failure_pts =match pid with | Some s-> [s] | _ -> []; 
   })), Failure)
   end
   end (*end for c1 not equal c2*)
   end (*end of match at root*)
   else if !Globals.use_coercion then (* there is a match at some node, but not at root *)
   begin
   Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: there is a match at some node, but not at root\n") pos;
   let res, prfs = do_coercion c1 c2 prog estate conseq ctx0 resth1 resth2 anode (*lhs_p lhs_t lhs_fl lhs_br rhs_p rhs_t rhs_fl*) lhs_b rhs_b ln2 is_folding pos pid in
   let prf = mkCoercion2 ctx0 conseq prfs in
   (res, prf)
   end
   else
   (CF.mkFailCtx_in (Basic_Reason ({
   fc_message = "there is a match at some node, not at root";
   fc_current_lhs = estate;
   fc_prior_steps = estate.es_prior_steps;
   fc_orig_conseq = estate.es_orig_conseq;
   fc_current_conseq = conseq;
   fc_failure_pts =match pid with | Some s-> [s] | _ -> [];})), NoAlias)
(* | Hole _ -> report_error pos *)
(* 	  ("heap_entail_conjunct: hole in the context") *)
(* | Star _ -> report_error pos *)
(* 	  ("heap_entail_conjunct: star in the context") *)
(* | Phase _ -> report_error pos *)
(* 	  ("heap_entail_conjunct: phase in the context") *)
(* | Hole _ -> report_error pos *)
(* 	  ("heap_entail_conjunct: hole in the context") *)
(* | Conj _ -> report_error pos *)
(* 	  ("heap_entail_conjunct: conj in the context") *)
(* | HTrue -> report_error pos *)
(* 	  ("heap_entail_conjunct: true in the context") *)
(* | HFalse -> report_error pos *)
(* 	  ("heap_entail_conjunct: false in the context")     *)
   | _ -> report_error pos
   ("heap_entail_conjunct: something wrong has happened with the context") in

(*****************************************************************************************************************************************)
(* end of check_aliased_node *)
(*****************************************************************************************************************************************)
(* check_node_helper *)
(*****************************************************************************************************************************************)
(* check one match *)
   let rec check_node_helper (all_nodes : (Context.match_res*Context.action) list) : (list_context * proof list) =
   match all_nodes with
   | ((rest_heap, anode, holes, r_flag),act) :: rest ->
   let rs1, prf1 = check_aliased_node (anode, r_flag) rest_heap act in
(* push the current holes in the estate *)
   let rs1 = Context.push_crt_holes_list_ctx rs1 holes in 
(* update the ctx frame *)
   if rest=[] then (rs1,[prf1])
   else  
   if !Globals.use_set then (* use_set denotes set of state searching *)
   let rs2,prfs2 = check_node_helper rest in
   (fold_context_left [rs1;rs2],prf1 :: prfs2)               
   else (rs1,[prf1])
   | [] -> (CF.mkFailCtx_in(Trivial_Reason "impossible here : end of check_node_helper"),[]) in
(* finally, check all matches  *)
   let rs, prfs = check_node_helper matches in
   let prf =
   if Gen.is_empty (List.tl prfs) then List.hd prfs
   else mkMMatch ctx0 conseq ln2 prfs
   in

(* need to modify the current state from rs, such that crt_ctx is being used *)
   (rs, prf)
   end
   end
   | HFalse | HTrue | Star _ | Conj _ | Phase _ | Hole _ -> report_error pos ("heap_entail_conjunct: "
   ^ "something bad has happened to split_linear_node") *)


(*******************************************************************************************************************************************************************************************)
(*
  Summary of the coercion helper methods:
  - check the guard in do_universal and rewrite_coercion
  -  rewrite_coercion called in apply_left_coercion and apply_right_coercion
  - apply_left_coercion called in do_coercion
  - apply_right_coercion called in do_coercion
  - do_coercion called in heap_entail_non_empty_rhs_heap --------- the main coercion helper
  - do_universal called in apply_universal
  - apply_universal called in do_coercion

*)

(* helper functions for coercion *)

(*
  Applying universally-quantified lemmas. Here are the steps:
  - Compute the set of universal variables. If the set is
  empty, then just do normal rewriting. (this has been done by apply_universal).
  - Split the guard out. Change it to existential to check
  for satisfiability.
  - Do the rewriting.
  - Perform entailment with rewritten formula
  - Filter subformulas from the pure part of the consequent
  that are related to the guard. This provides us with the instantiation.

  Now it only works when applying to the antecedent.
*)
(* new version:
   - forall v*. H /\ G -> B
   - match H and the node/predicate to be coerced and obtain the substitution \rho
*)					
(*******************************************************************************************************************************************************************************************)
(* do_universal *)
(*******************************************************************************************************************************************************************************************)
(*
  node - h_formulae?
  f - formula?
  coer - lemma
  anode - LHS node to unfold
  lhs_b - LHS base
  rhs_b - RHS base
  conseq - consequent
  bool - folding?
  pid - formula label?
*)
and do_universal prog estate node rest_of_lhs coer anode lhs_b rhs_b conseq is_folding pos: (list_context * proof) =
  begin
    (* rename the bound vars *)
    let f_univ_vars = CP.fresh_spec_vars coer.coercion_univ_vars in
    (*
	  let _ = print_string ("univ_vars: "   ^ (String.concat ", "   (List.map CP.name_of_spec_var  coer.coercion_univ_vars)) ^ "\n") in
    *)
    (*let _ = print_string ("[do_univ]: rename the univ boudn vars: " ^ (String.concat ", " (List.map CP.name_of_spec_var f_univ_vars)) ^ "\n") in	*)
    let tmp_rho = List.combine coer.coercion_univ_vars f_univ_vars in
    let coer_lhs = CF.subst tmp_rho coer.coercion_head in
    let coer_rhs = CF.subst tmp_rho coer.coercion_body in
    (************************************************************************)
    (* also rename the free vars from the rhs that do not appear in the lhs *)
    let lhs_fv = (fv_rhs coer_lhs coer_rhs) in
    let fresh_lhs_fv = CP.fresh_spec_vars lhs_fv in
    let tmp_rho = List.combine lhs_fv fresh_lhs_fv in
    let coer_lhs = CF.subst tmp_rho coer_lhs in
    let coer_rhs = CF.subst tmp_rho coer_rhs in
    let lhs_heap, lhs_guard,lhs_fl, _, lhs_branches, _  = split_components coer_lhs in
    let lhs_guard = MCP.fold_mem_lst (CP.mkTrue no_pos) false false (* true true *) lhs_guard in
    match node, lhs_heap with
	  | ViewNode ({ h_formula_view_node = p1;
		h_formula_view_name = c1;
		h_formula_view_origins = origs;
		h_formula_view_remaining_branches = br1;
		h_formula_view_arguments = ps1} as h1),
        ViewNode ({ h_formula_view_node = p2;
		h_formula_view_name = c2;
		h_formula_view_remaining_branches = br2;
		h_formula_view_arguments = ps2} as h2) when CF.is_eq_view_name(*is_eq_view_spec*) h1 h2 (*c1=c2 && (br_match br1 br2) *) -> begin
	      (* the lemma application heuristic:
	         - if the flag lemma_heuristic is true then we use both coerce& match - each lemma application must be followed by a match  - and history
	         - if the flag is false, we only use coerce&distribute&match
	      *)
	      let apply_coer = (coer_target prog coer anode (CF.formula_of_base rhs_b) (CF.formula_of_base lhs_b)) in
          (* let f1=apply_coer in *)
          (* (\* let f2=(get_estate_must_match estate) in *\) *)
          (* let f3=List.mem coer.coercion_body_view origs in *)
          (* let f4=is_cycle_coer coer origs in *)
          (* let f5=is_distributive coer in *)
          (* let f6=(!enable_distribution) in *)
	      (* if (!Globals.lemma_heuristic && 		(\* use coerce&match together with the history mechanism *\) *)
		  (*     (not(apply_coer) 					(\* the target is not present *\) *)
		  (*     (\* or (get_estate_must_match estate) *\))  (\* must match *\) *)
		  (* && (List.mem coer.coercion_body_view origs *)
		  (* or is_cycle_coer coer origs)) (\* there is a cycle *\) *)
		  (*   or 	(not(!Globals.lemma_heuristic) &&   (\* use coerce&distribute&match*\) *)
		  (*       (not(apply_coer) or 				(\* the target is not present *\) *)
		  (*           ((\* (get_estate_must_match estate) 	(\\* must match *\\) *\) *)
		  (*           (\* &&  *\)(not(!enable_distribution) 		(\* distributive coercion is not allowed *\) *)
		  (*   	    or not(is_distributive coer))))) 	(\* coercion is not distributive *\) *)
          if (not(apply_coer) or (is_cycle_coer coer origs))
	      then
            (* let s = (pr_list string_of_bool [f1;f3;f4;f5;f6]) in *)
		    (Debug.devel_pprint("[do_universal]: Coercion cannot be applied!"(* ^s *)) pos; 
		    (CF.mkFailCtx_in(Basic_Reason( { 
				fc_message ="failed coercion application";
				fc_current_lhs = estate;
				fc_prior_steps = estate.es_prior_steps;
				fc_orig_conseq = estate.es_orig_conseq;
				fc_current_conseq = CF.formula_of_heap HFalse pos;
				fc_failure_pts = match (get_node_label node) with | Some s-> [s] | _ -> [];})), Failure))
	      else	(* we can apply coercion *)
		    begin
		      (* if (not(!Globals.lemma_heuristic) (\* && get_estate_must_match estate *\)) then *)
		      (*   ((\*print_string("disable distribution\n");*\) enable_distribution := false); *)
		      (* the \rho substitution \rho (B) and  \rho(G) is performed *)
		      let lhs_guard_new = CP.subst_avoid_capture (p2 :: ps2) (p1 :: ps1) lhs_guard in
		      let lhs_branches_new = List.map (fun (s, f) -> (s, (CP.subst_avoid_capture (p2 :: ps2) (p1 :: ps1) f))) lhs_branches in
		      let coer_rhs_new1 = subst_avoid_capture (p2 :: ps2) (p1 :: ps1) coer_rhs in
		      (* let coer_rhs_new = add_origins coer_rhs_new1 (coer.coercion_head_view :: origs) in *)
		      let coer_rhs_new = add_origins coer_rhs_new1 ((* coer.coercion_name ::  *)origs) in
		      let _ = reset_int2 () in
		      (*let xpure_lhs = xpure prog f in*)
		      (*************************************************************************************************************************************************************************)
		      (* delay the guard check *)
		      (* for now, just add it to the consequent *)
		      (*************************************************************************************************************************************************************************)
		      (*let guard_to_check = CP.mkExists f_univ_vars lhs_guard_new pos in*)
		      (*let _ = print_string("xpure_lhs: " ^ (Cprinter.string_of_pure_formula xpure_lhs) ^ "\n") in
		        let _ = print_string("guard: " ^ (Cprinter.string_of_pure_formula guard_to_check) ^ "\n") in*)
		      let new_f = normalize coer_rhs_new rest_of_lhs pos in
		      (* add the guard to the consequent  - however, the guard check is delayed *)
              (* ?? *)
		      let formula,to_aux_conseq = 
                if !allow_imm then (replace_branches lhs_branches_new (mkTrue (mkTrueFlow ()) pos),lhs_guard_new)
                else (replace_branches lhs_branches_new (formula_of_pure_N lhs_guard_new pos), CP.mkTrue pos) in
		      let new_conseq = normalize conseq formula pos in
		      let new_estate = {estate with
				  (* es_evars = f_univ_vars @ estate.es_evars; *)
				  (* the new universal vars to be instantiated *)
				  es_ivars = f_univ_vars @ estate.es_ivars;
				  es_formula = new_f;
				  (* es_aux_conseq = CP.mkAnd estate.es_aux_conseq to_aux_conseq pos; *)
				  (* es_must_match = true *)} in
		      let new_ctx = Ctx new_estate in
		      let res, prf = heap_entail prog is_folding (SuccCtx [new_ctx]) new_conseq pos in
		      (add_to_aux_conseq res to_aux_conseq pos, prf)
		    end
	    end
	  | _ -> (CF.mkFailCtx_in(Basic_Reason ( { 
			fc_message ="failed coercion application, found data but expected view";
			fc_current_lhs = estate;
			fc_prior_steps = estate.es_prior_steps;
			fc_orig_conseq = estate.es_orig_conseq;
			fc_current_conseq = CF.formula_of_heap HFalse pos;
			fc_failure_pts = [];})), Failure)
  end


and is_cycle_coer (c:coercion_decl) (origs:ident list) : bool =  
  Gen.Debug.no_2 "is_cycle_coer" Cprinter.string_of_coercion Cprinter.str_ident_list string_of_bool
      is_cycle_coer_a c origs

(* this checks if node is being applied a second time with same coercion rule *)
and is_cycle_coer_a (c:coercion_decl) (origs:ident list) : bool =  List.mem c.coercion_name origs

and is_original_match_a anode ln2 = 
  (get_view_original anode) || (get_view_original ln2)

and is_original_match anode ln2 = 
  let p = Cprinter.string_of_h_formula in
  Gen.Debug.no_2 "is_original_match"
      p p
      string_of_bool
      (fun _ _ -> is_original_match_a anode ln2) anode ln2

(*
  Rewrites f by matching node with coer_lhs to obtain a substitution.
  The substitution is then applied to coer_rhs, which is then *-joined
  with f and then normalized.

  If the first component of the returned value is true, the rewrite
  is successful and the coercion performed. Otherwise, the rewrite is
  not performed (due to the guard).
*)
(*******************************************************************************************************************************************************************************************)
(* rewrite_coercion *)
(*******************************************************************************************************************************************************************************************)
and rewrite_coercion prog estate node f coer lhs_b rhs_b target_b weaken pos : (bool * formula) =
  let p1 = Cprinter.string_of_formula in
  let p2 = pr_pair string_of_bool Cprinter.string_of_formula in
  Gen.Debug.no_2 "rewrite_coercion" Cprinter.string_of_h_formula  p1 p2 (fun _ _ -> rewrite_coercion_x prog estate node f coer lhs_b rhs_b target_b weaken pos) node f 

and rewrite_coercion_x prog estate node f coer lhs_b rhs_b target_b weaken pos : (bool * formula) =
  (* This function also needs to add the name and the origin list
     of the source view to the origin list of the target view. It
     needs to check if the target view in coer_rhs belongs to the
     list of origins of node. If so, don't apply the coercion *)
  (******************** here it was the test for coerce&match *************************)
  let coer_lhs = coer.coercion_head in
  let coer_rhs = coer.coercion_body in
  let lhs_heap, lhs_guard, lhs_flow, lhs_pr, lhs_branches, _ = split_components coer_lhs in
  let lhs_guard = MCP.fold_mem_lst (CP.mkTrue no_pos) false false (* true true *) lhs_guard in  (* TODO : check with_dupl, with_inv *)
  match node, lhs_heap with
    | ViewNode ({ h_formula_view_node = p1;
      h_formula_view_name = c1;
      h_formula_view_origins = origs;
      h_formula_view_original = original;
      h_formula_view_remaining_branches = br1;
      h_formula_view_arguments = ps1} as h1),
	  ViewNode ({ h_formula_view_node = p2;
      h_formula_view_name = c2;
      h_formula_view_remaining_branches = br2;
      h_formula_view_arguments = ps2} as h2) 
          when CF.is_eq_view_name(*is_eq_view_spec*) h1 h2  (* c1=c2 && (br_match br1 br2) *)-> begin
	        (*************************************************************)
	        (* replace with the coerce&match mechanism *)
	        (*************************************************************)
	        let apply_coer = (coer_target prog coer node (CF.formula_of_base target_b (* rhs_b *)) (CF.formula_of_base lhs_b)) in
	        (* the lemma application heuristic:
	           - if the flag 	lemma_heuristic in true then we use both coerce& match and history
	           - if the flag is false, we only use coerce&distribute&match
	        *)
            (* let f1=apply_coer in *)
            (* (\* let f2=(get_estate_must_match estate) in *\) *)
            (* let f3=List.mem coer.coercion_body_view origs in *)
            (* let f4=is_cycle_coer coer origs in *)
            (* let f5=is_distributive coer in *)
            (* let f6=(!enable_distribution) in *)
	        (* if (!Globals.lemma_heuristic &&  *)
            (*     (not(apply_coer) (\* coerce&match+history *\) (\* or (get_estate_must_match estate) *\)) &&  *)
            (*     (List.mem coer.coercion_body_view origs  *)
            (*     or (\* List.mem coer.coercion_head_view origs *\)  (is_cycle_coer coer origs)) *)
            (* ) *)
	        (*   or (not(!Globals.lemma_heuristic) && (\* coerce&distribute&match *\) *)
		    (*       (not(apply_coer) or 	(\* the target is not present *\) *)
			(*           (false (\* (get_estate_must_match estate) *\) (\* must match *\) && (not(!enable_distribution) (\* distributive coercion is not allowed *\) *)
			(* 		  or not(is_distributive coer))))) (\* coercion is not distributive *\) *)
            (* when disabled --imm failed and vice-versa! *)
            let flag = if !Globals.allow_imm then false else not(apply_coer) in
            if (flag or(is_cycle_coer coer origs))
	        then
              (* let s = (pr_list string_of_bool [f1;(\* f2; *\)f3;f4;f5;f6]) in *)
		      (Debug.devel_pprint("[rewrite_coercion]: Rewrite cannot be applied!"(* ^s *)) pos; (false, mkTrue (mkTrueFlow ()) no_pos))
	        else
		      (* we can apply coercion *)
		      begin
		        (* apply \rho (G)	and \rho(B) *)
		        let lhs_guard_new = CP.subst_avoid_capture (p2 :: ps2) (p1 :: ps1) lhs_guard in
		        (*let lhs_branches_new = List.map (fun (s, f) -> (s, (CP.subst_avoid_capture (p2 :: ps2) (p1 :: ps1) f))) lhs_branches in*)
		        let coer_rhs_new1 = subst_avoid_capture (p2 :: ps2) (p1 :: ps1) coer_rhs in
		        (* let coer_rhs_new = add_origins coer_rhs_new1 (coer.coercion_head_view :: origs) in *)
		        let coer_rhs_new = add_origins coer_rhs_new1 ((* coer.coercion_name ::  *)origs) in
		        let _ = reset_int2 () in
		        let xpure_lhs, xpure_lhs_b, _, memset = xpure prog f in
		        let xpure_lhs = MCP.fold_mem_lst (CP.mkTrue no_pos) true true xpure_lhs in 
		        (*******************************************************************************************************************************************************************************************)
		        (* test the guard again in rewrite_coercion
		           - for now we only revise the universal lemmas handled by apply_universal --> the check stays here as it is *)
		        (*******************************************************************************************************************************************************************************************)
		        (* is it necessary to xpure (node * f) instead ? *)

		        (* ok because of TP.imply*)
		        if ((imply_formula_no_memo xpure_lhs lhs_guard_new !imp_no memset)) then
		          (*if ((fun (c1,_,_)-> c1) (TP.imply xpure_lhs lhs_guard_new (string_of_int !imp_no) false)) then*)
		          let new_f = normalize coer_rhs_new f pos in
			      (* if (not(!Globals.lemma_heuristic) (\* && get_estate_must_match estate *\)) then *)
			      (*   ((\*print_string("disable distribution\n"); *\)enable_distribution := false); *)
			      (true, new_f)
		        else if !Globals.case_split then begin
		          (*
		            Doing case splitting based on the guard.
		          *)
		          Debug.devel_pprint
		              ("rewrite_coercion: guard is not satisfied, " ^ "splitting.\n") pos;
		          let neg_guard = CP.mkNot lhs_guard_new None pos in
                  let node = ViewNode{h1 with h_formula_view_remaining_branches=None; h_formula_view_pruning_conditions=[];} in
		          let f0 = normalize f (formula_of_heap node pos) pos in
		          let f1 = normalize f0 (formula_of_mix_formula (MCP.mix_of_pure neg_guard) (Cperm.mkTrue pos) pos) pos in
			      (* unfold the case with the negation of the guard. *)
		          let f1 = unfold_nth 2 (prog,None) f1 p1 true 0 pos in
		          let f2 = normalize f0 (formula_of_mix_formula (MCP.mix_of_pure lhs_guard_new) (Cperm.mkTrue pos) pos) pos in
			      (* f2 need no unfolding, since next time coercion is reapplied, the guard is guaranteed to be satisified *)
		          let new_f = mkOr f1 f2 pos in
			      (* if (not(!Globals.lemma_heuristic) (\* && (get_estate_must_match estate) *\)) then *)
			      (*   ((\*print_string("disable distribution\n"); *\)enable_distribution := false); *)
			      (true, new_f)
		        end else begin
		          Debug.devel_pprint
		              ("rewrite_coercion: guard is not satisfied, " ^ "no splitting.\n") pos;
		          (false, mkTrue (mkTrueFlow ()) no_pos)
		        end
		      end
          end
    | _ -> (false, mkTrue (mkTrueFlow ()) no_pos)
	      (*end	*)

and apply_universal prog estate coer resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 c2 conseq is_folding pos =
  let pr (e,_) = Cprinter.string_of_list_context e in
  Gen.Debug.no_3 "apply_universal"  Cprinter.string_of_h_formula Cprinter.string_of_h_formula (fun x -> x) pr 
      (fun _ _ _ -> apply_universal_a prog estate coer resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 c2 conseq is_folding pos)
      anode resth1 c2
      (* anode - chosen node, resth1 - rest of heap *)

(*******************************************************************************************************************************************************************************************)
and apply_universal_a prog estate coer resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 c2 conseq is_folding pos =
  (*******************************************************************************************************************************************************************************************)
  let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_pr,lhs_br) = CF.extr_formula_base lhs_b in
  flush stdout;
  if Gen.is_empty coer.coercion_univ_vars then (CF.mkFailCtx_in ( Basic_Reason (  {
	  fc_message = "failed apply_universal : not a universal rule";
	  fc_current_lhs = estate;
	  fc_prior_steps = estate.es_prior_steps;
	  fc_orig_conseq = estate.es_orig_conseq;
	  fc_current_conseq = CF.formula_of_heap HFalse pos; 
	  fc_failure_pts = match (get_node_label anode) with | Some s-> [s] | _ -> [];
  })), Failure)
  else begin
    let f = mkBase resth1 lhs_p lhs_t lhs_fl lhs_pr lhs_br pos in(* Assume coercions have no branches *)
    let estate = CF.moving_ivars_to_evars estate anode in
    let _ = Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: apply_universal: "	^ "c1 = " ^ c1 ^ ", c2 = " ^ c2 ^ "\n") pos in
    (*do_universal anode f coer*)
    do_universal prog estate anode f coer anode lhs_b rhs_b conseq is_folding pos
  end


(*******************************************************************************************************************************************************************************************)
(* do_coercion *)
(*******************************************************************************************************************************************************************************)

and find_coercions_x c1 c2 prog anode ln2 =
  let origs = try get_view_origins anode with _ -> print_string "exception get_view_origins\n"; [] in 
  let coers1 = look_up_coercion_def_raw prog.prog_left_coercions c1 in
  let coers1 = List.filter (fun c -> not(is_cycle_coer c origs)) coers1  in (* keep only non-cyclic coercion rule *)
  let origs2 = try get_view_origins ln2 with _ -> print_string "exception get_view_origins\n"; [] in 
  let coers2 = look_up_coercion_def_raw prog.prog_right_coercions c2 in
  let coers2 = List.filter (fun c -> not(is_cycle_coer c origs2)) coers2  in (* keep only non-cyclic coercion rule *)
  let coers1, univ_coers = List.partition (fun c -> Gen.is_empty c.coercion_univ_vars) coers1 in
  (* let coers2 = (* (List.map univ_to_right_coercion univ_coers)@ *)coers2 in*)
  ((coers1,coers2),univ_coers)

and find_coercions c1 c2 prog anode ln2 =
  let p1 = Cprinter.string_of_h_formula in
  let p = (fun l -> string_of_int (List.length l)) in 
  let p2 (v,_) = pr_pair p p v in
  Gen.Debug.no_2 "find_coercions" p1 p1 p2 (fun _ _ -> find_coercions_x c1 c2 prog anode ln2 ) anode ln2

and do_coercion prog c_opt estate conseq resth1 resth2 anode lhs_b rhs_b ln2 is_folding pos : (CF.list_context * proof list) =
  let pr (e,_) = Cprinter.string_of_list_context e in
  Gen.Debug.no_5 "do_coercion" (* prid prid  *)Cprinter.string_of_h_formula Cprinter.string_of_h_formula Cprinter.string_of_h_formula 
      Cprinter.string_of_h_formula Cprinter.string_of_formula_base pr
      (fun _ _ _ _ _ -> do_coercion_x prog c_opt estate conseq resth1 resth2 anode lhs_b rhs_b ln2 is_folding pos) anode resth1 ln2 resth2 rhs_b

and do_coercion_x prog c_opt estate conseq resth1 resth2 anode lhs_b rhs_b ln2 is_folding pos : (CF.list_context * proof list) =
  (* let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_br) = CF.extr_formula_base lhs_b in *)
  (* let (rhs_h,rhs_p,rhs_t,rhs_fl,rhs_br) = CF.extr_formula_base rhs_b in *)
  let ctx0 = Ctx estate in
  let c1 = get_node_name anode in
  let c2 = get_node_name ln2 in
  let ((coers1,coers2),univ_coers) = match c_opt with
    | None -> find_coercions c1 c2 prog anode ln2 
    | Some c -> match c.coercion_type with
        | Iast.Left -> if c.coercion_univ_vars == [] then (([c],[]),[])
          else (([],[]),[c])
        | Iast.Right -> (([],[c]),[])
        | _ -> report_error no_pos ("Iast.Equiv detected - astsimpl should have eliminated it ")
  in 
  if ((List.length coers1)=0 && (List.length coers2)=0  && (List.length univ_coers)=0 )
    || not(is_original_match anode ln2)
  then (CF.mkFailCtx_in(Trivial_Reason "no lemma found in both LHS and RHS nodes (do coercion)"), [])
  else begin 
    Debug.devel_pprint ("do_coercion: estate :" ^ (Cprinter.string_of_entail_state estate) ^ "\n") pos;
    Debug.devel_pprint ("do_coercion: " ^ "c1 = " ^ c1 ^ ", c2 = " ^ c2 ^ "\n") pos;
    (* get origins of a node *)
    (* let origs = try get_view_origins anode with _ -> print_string "exception get_view_origins\n"; [] in  *)
    (* let coers1 = look_up_coercion_def_raw prog.prog_left_coercions c1 in *)
    (* let coers1 = List.filter (fun c -> not(is_cycle_coer c origs)) coers1  in (\* keep only non-cyclic coercion rule *\) *)
    (* let coers1, univ_coers = List.partition (fun c -> Gen.is_empty c.coercion_univ_vars) coers1 in *)
    (* universal coercions *)
    (*let _ = print_string("[do_coercion]: number of univ coer " ^ (string_of_int (List.length univ_coers)) ^ "--> call apply universal \n") in*)
    let univ_r = if (List.length univ_coers)>0 then
      let univ_res_tmp = List.map (fun coer -> apply_universal prog estate coer resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 c2 conseq is_folding pos) univ_coers in
      let univ_res, univ_prf = List.split univ_res_tmp in
      Some (univ_res, univ_prf)
    else None in
    (*let univ_prf = List.concat univ_prf in*)
    (* left coercions *)
    (*let _ = print_string("[do_coercion]: number of univ coer " ^ (string_of_int (List.length coers1)) ^ "--> call apply_left_coercion\n") in  *)
    let left_r = if (List.length coers1)>0 then
      let tmp1 = List.map  (fun coer -> apply_left_coercion estate coer prog conseq ctx0 resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 is_folding pos) coers1 in
      let left_res, left_prf = List.split tmp1 in
      let left_prf = List.concat left_prf in
      Some (left_res,left_prf)
    else None in
    (* a quick hack *)
    (* right coercions *)
    (* let origs2 = try get_view_origins ln2 with _ -> print_string "exception get_view_origins\n"; [] in  *)
    (* let coers2 = look_up_coercion_def_raw prog.prog_right_coercions c2 in *)
    (* let coers2 = List.filter (fun c -> not(is_cycle_coer c origs2)) coers2  in (\* keep only non-cyclic coercion rule *\) *)
    let right_r = if (List.length coers2)>0 then
      let tmp2 = List.map (fun coer -> apply_right_coercion estate coer prog conseq ctx0 resth2 ln2 (*rhs_p rhs_t rhs_fl*) lhs_b rhs_b c2 is_folding pos) coers2 in
      let right_res, right_prf = List.split tmp2 in
      let right_prf = List.concat right_prf in
      Some (right_res,right_prf)
    else None in
    let proc lst = 
      let r1 = List.map (fun (c,p) -> (fold_context_left c,p)) lst in
      let (r2,p) = List.split r1 in
      let res = fold_context_left r2 in
      let final_res = (isFailCtx res) in
      let prf = List.concat (List.map (fun (c,p) -> if final_res==(isFailCtx c) then p else []) r1) in
      (res,prf) in
    let m = List.fold_right (fun x r -> match x with None -> r | Some x -> x::r ) [univ_r;left_r;right_r] [] in
    if m==[] then (CF.mkFailCtx_in(Trivial_Reason "cannot find matching node in antecedent (do coercion)"), [])
    else proc m
  end
    (* match univ_r,left_r,right_r with *)
	(*     (\* | None,None,None -> (CF.mkFailCtx_in(Basic_Reason None), []) *\) *)
    (*   | None,None,None -> (CF.mkFailCtx_in(Trivial_Reason "cannot find matching node in antecedent (do coercion)"), []) *)
	(*         (\* (CF.mkFailCtx_in(Basic_Reason ( { *\) *)
	(*         (\* fc_message ="cannot find matching node in antecedent (do coercion) "; *\) *)
	(*         (\* fc_current_lhs = estate; *\) *)
	(*         (\* fc_orig_conseq = struc_formula_of_formula conseq pos; *\) *)
	(*         (\* fc_failure_pts = match pid with | Some s-> [s] | _ -> [];})), []) *\) *)
    (*   | Some (c1,c2), None, None  *)
    (*   | None, Some (c1,c2), None   *)
    (*   | None, None, Some (c1,c2) -> ((fold_context_left c1),c2) *)
    (*   | Some (c1,c2),Some(d1,d2),None *)
    (*   | Some (c1,c2),None,Some(d1,d2) *)
    (*   | None,Some (c1,c2),Some(d1,d2) ->  *)
    (*         let c1 = (fold_context_left c1) in *)
    (*         let d1 = (fold_context_left d1) in *)
    (*         let r = (fold_context_left [c1;d1]) in *)
    (*         let prf = (if (isFailCtx r)==(isFailCtx c1) then c2 else [])@ *)
    (*           (if (isFailCtx r)==(isFailCtx d1) then d2 else [])in *)
    (*         (r,prf) *)
    (*   | Some (c1,c2),Some(d1,d2),Some (e1,e2) -> *)
    (*         let c1 = (fold_context_left c1) in *)
    (*         let d1 = (fold_context_left d1) in *)
    (*         let e1 = (fold_context_left e1) in *)
    (*         let r = (fold_context_left [c1;d1;e1]) in *)
    (*         let prf = (if (isFailCtx r)==(isFailCtx c1) then c2 else [])@ *)
    (*           (if (isFailCtx r)==(isFailCtx d1) then d2 else [])@ *)
    (*           (if (isFailCtx r)==(isFailCtx e1) then e2 else [])in *)
    (*         (r,prf) *)
	(*******************************************************************************************************************************************************************************************)
	(* apply_left_coercion *)
	(*******************************************************************************************************************************************************************************************)
and apply_left_coercion estate coer prog conseq ctx0 resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 is_folding pos=
  let pr (e,_) = Cprinter.string_of_list_context e in
  Gen.Debug.no_3 "apply_left_coercion" Cprinter.string_of_h_formula Cprinter.string_of_h_formula Cprinter.string_of_coercion pr
      (fun _ _ _ -> apply_left_coercion_a estate coer prog conseq ctx0 resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 is_folding pos)
      anode resth1 coer
      (* anode - LHS matched node
         resth1 - LHS remainder
         lhs_p - lhs mix pure
         lhs_t - type of formula? (for OO)
         lhs_fl - flow 
         lhs_br - lhs branches
         lhs_b - lhs base
         rhs_b - rhs base
         c1 - lhs pred name
         is_folding
         pos 
         pid - ?id
      *)
and apply_left_coercion_a estate coer prog conseq ctx0 resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 is_folding pos=
  let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_pr, lhs_br) = CF.extr_formula_base lhs_b in
  (*let _ = print_string("left coercion\n") in*)
  let f = mkBase resth1 lhs_p lhs_t lhs_fl lhs_pr lhs_br pos in
  let _ = Debug.devel_pprint ("heap_entail_non_empty_rhs_heap: "
  ^ "left_coercion: c1 = "
  ^ c1 ^ "\n") pos in
  let ok, new_lhs = rewrite_coercion prog estate anode f coer lhs_b rhs_b rhs_b true pos in
  if ok then begin
    let new_ctx1 = build_context ctx0 new_lhs pos in
	(* let new_ctx = set_context_formula ctx0 new_lhs in *)
    let new_ctx = SuccCtx[((* set_context_must_match *) new_ctx1)] in
    let res, tmp_prf = heap_entail prog is_folding new_ctx conseq pos in
    let prf = mkCoercionLeft ctx0 conseq coer.coercion_head
	  coer.coercion_body tmp_prf coer.coercion_name
    in
	(res, [prf])
  end else (CF.mkFailCtx_in( Basic_Reason ( { 
	  fc_message ="failed left coercion application";
	  fc_current_lhs = estate;
	  fc_prior_steps = estate.es_prior_steps;
	  fc_orig_conseq = estate.es_orig_conseq;
	  fc_current_conseq = CF.formula_of_heap HFalse pos; 
	  fc_failure_pts = match (get_node_label anode) with | Some s-> [s] | _ -> [];})), [])
    (*******************************************************************************************************************************************************************************************)
    (* apply_right_coercion *)
    (*******************************************************************************************************************************************************************************************)
and apply_right_coercion estate coer prog (conseq:CF.formula) ctx0 resth2 ln2 (*rhs_p rhs_t rhs_fl*) lhs_b rhs_b (c2:ident) is_folding pos =
  let pr (e,_) = Cprinter.string_of_list_context e in
  Gen.Debug.no_3 "apply_right_coercion" Cprinter.string_of_h_formula Cprinter.string_of_h_formula Cprinter.string_of_coercion 
      (* Cprinter.string_of_formula (fun x -> x)  *)pr
      (fun _ _ _ -> apply_right_coercion_a estate coer prog (conseq:CF.formula) ctx0 resth2 ln2 (*rhs_p rhs_t rhs_fl*) lhs_b rhs_b (c2:ident) is_folding pos) ln2 resth2 coer (* conseq c2 *)

(* ln2 - RHS matched node
   resth2 - RHS remainder
   rhs_p - lhs mix pure
   rhs_t - type of formula? (for OO)
   rhs_fl - flow 
   ?rhs_br - not present? why?
   lhs_b - lhs base
   rhs_b - rhs base
   c2 - rhs pred name
   is_folding
   pos 
   pid - ?id
*)
and apply_right_coercion_a estate coer prog (conseq:CF.formula) ctx0 resth2 ln2 (*rhs_p rhs_t rhs_fl*) lhs_b rhs_b (c2:ident) is_folding pos =
  let (_,rhs_p,rhs_t,rhs_fl,rhs_pr, rhs_br) = CF.extr_formula_base rhs_b in
  (*let _ = print_string("right coercion\n") in*)
  let f = mkBase resth2 rhs_p rhs_t rhs_fl rhs_pr [] pos in
  let _ = Debug.devel_pprint ("do_right_coercion : c2 = "
  ^ c2 ^ "\n") pos in
  (* if is_coercible ln2 then *)
  let ok, new_rhs = rewrite_coercion prog estate ln2 f coer lhs_b rhs_b lhs_b false pos in
  if (is_coercible ln2)&&ok  then begin
    (* need to make implicit var become explicit *)
    let vl = Gen.BList.intersect_eq CP.eq_spec_var estate.es_gen_impl_vars (h_fv ln2) in
    let new_iv = Gen.BList.difference_eq CP.eq_spec_var estate.es_gen_impl_vars vl in
    let _ = if not(vl==[]) then Debug.devel_pprint ("do_right_coercion : impl to expl vars  " ^ (Cprinter.string_of_spec_var_list vl) ^ "\n") pos in
    let nctx = set_context (fun es -> {es with (* es_must_match = true; *)
        es_gen_impl_vars = new_iv; es_gen_expl_vars =  (es.es_gen_expl_vars@vl)}) ctx0 in
	let new_ctx = SuccCtx [nctx] (* (set_context_must_match ctx0)] *) in
	let res, tmp_prf = heap_entail prog is_folding new_ctx new_rhs pos in
    let res = set_list_context (fun es -> {es with (* es_must_match = estate.es_must_match; *)
        (* es_gen_impl_vars = estate.es_gen_impl_vars;  *)es_gen_expl_vars =  estate.es_gen_expl_vars}) res in
	let prf = mkCoercionRight ctx0 conseq coer.coercion_head
	  coer.coercion_body tmp_prf  coer.coercion_name
	in
	(res, [prf])
  end else 
    let _ = Debug.devel_pprint ("do_right_coercion :  " ^ c2 ^ "failed \n") pos in
    (CF.mkFailCtx_in(Basic_Reason ( {fc_message ="failed right coercion application";
    fc_current_lhs = estate;
    fc_prior_steps = estate.es_prior_steps;
    fc_orig_conseq = estate.es_orig_conseq;
    fc_current_conseq = CF.formula_of_heap HFalse pos;
    fc_failure_pts = match (get_node_label ln2) with | Some s-> [s] | _ -> [];})), [])
        (* else (CF.mkFailCtx_in(Basic_Reason ({fc_message ="failed right coercion application"; *)
        (* fc_current_lhs = estate; *)
        (* fc_prior_steps = estate.es_prior_steps; *)
        (* fc_orig_conseq = estate.es_orig_conseq; *)
        (* fc_current_conseq = CF.formula_of_heap HFalse pos; *)
        (* fc_failure_pts = match pid with | Some s-> [s] | _ -> [];})), [])  *)
        (*************************************************************************************************************************
                                                                                                                                  05.06.2008:
                                                                                                                                  Utilities for existential quantifier elimination:
                                                                                                                                  - before we were only searching for substitutions of the form v1 = v2 and then substitute ex v1. P(v1) --> P(v2)
                                                                                                                                  - now, we want to be more aggressive and search for substitutions of the form v1 = exp2; however, we can only apply these substitutions to the pure part
                                                                                                                                  (due to the way shape predicates are recorded --> root pointer and args are suppose to be spec vars)
                                                                                                                                  - also check that v1 is not contained in FV(exp2)
        *************************************************************************************************************************)

(* apply elim_exist_exp_loop until no change *)
and elim_exists_exp (f0 : formula) : (formula) =
  let rec perm_helper f0 = match f0 with
  | Or ({ formula_or_f1 = f1;formula_or_f2 = f2;formula_or_pos = pos}) -> mkOr (perm_helper f1) (perm_helper f2) pos
  | Base _ -> f0
  | Exists e->
        let hfv = h_fv e.formula_exists_heap in
        let l2,l1 = List.partition (fun v-> List.exists (CP.eq_spec_var v) hfv) e.formula_exists_qvars in
        let rqv, pp1 = Cperm.elim_exists_perm l1 e.formula_exists_perm in
        mkExists (rqv@l2) e.formula_exists_heap e.formula_exists_pure e.formula_exists_type e.formula_exists_flow pp1 e.formula_exists_branches e.formula_exists_pos in   
  let f, flag = elim_exists_exp_loop f0 in
  if flag then (elim_exists_exp f)
  else perm_helper f 

(* removing existentail using ex x. (x=e & P(x)) <=> P(e) *)
and elim_exists_exp_loop (f0 : formula) : (formula * bool) = match f0 with
  | Or ({formula_or_f1 = f1;
	formula_or_f2 = f2;
	formula_or_pos = pos}) ->
        let ef1, flag1 = elim_exists_exp_loop f1 in
        let ef2, flag2 = elim_exists_exp_loop f2 in
	    (mkOr ef1 ef2 pos, flag1 & flag2)
  | Base _ -> (f0, false)
  | Exists ({ formula_exists_qvars = qvar :: rest_qvars;
	formula_exists_heap = h;
	formula_exists_pure = p;
	formula_exists_type = t;
	formula_exists_perm = pr;
	formula_exists_branches = b;
	formula_exists_flow = fl;
	formula_exists_pos = pos}) ->
        let fvh = h_fv h in
	    (*let _ = print_string("Try to eliminate " ^ Cprinter.string_of_spec_var qvar ^ "\n") in*)
	    if  not(List.exists (fun sv -> CP.eq_spec_var sv qvar) fvh) then
	      (*List.mem qvar fvh)	then*) (* if it does not appear in the heap part --> we try to eliminate *)
	      (*let _ = print_string("fv(h) = " ^ Cprinter.string_of_spec_var_list fvh ^ "\n") in*)
	      let st, pp1 = MCP.get_subst_equation_mix_formula p qvar false in
	      if List.length st > 0 then (* if there exists one substitution  - actually we only take the first one -> therefore, the list should only have one elem *)
	        (* basically we only apply one substitution *)
	        let one_subst = List.hd st in
		    (*let _ = print_string ("\nLength = " ^ string_of_int (List.length st) ^ "\n") in
		      let _ =  print_string("\n Using the subst var: " ^ Cprinter.string_of_spec_var (fst one_subst) ^ "\texp: " ^ Cprinter.string_of_formula_exp (snd one_subst) ^ "\n") in*)
	        let tmp = mkBase h pp1 t fl pr b pos in
		    (*let _ = (print_string (" Base formula: " ^ (Cprinter.string_of_formula tmp) ^ "\n")) in*)
	        let new_baref = subst_exp [one_subst] tmp in
 		    (*let _ = (print_string (" new_baref: " ^ (Cprinter.string_of_formula new_baref) ^ "\n")) in*)
	        let tmp2 = add_quantifiers rest_qvars new_baref in
	        let tmp3, _ = elim_exists_exp_loop tmp2 in
		    (tmp3, true)
	      else (* if qvar is not equated to any variables, try the next one *)
	        let tmp1 = mkExists rest_qvars h p t fl pr b pos in
	        let tmp2, flag = elim_exists_exp_loop tmp1 in
	        let tmp3 = add_quantifiers [qvar] tmp2 in
		    (tmp3, flag)
	    else (* anyway it's going to stay in the heap part so we can't eliminate --> try eliminate the rest of them, and then add it back to the exist quantified vars *)
	      let tmp1 = mkExists rest_qvars h p t fl pr b pos in
	      let tmp2, flag = elim_exists_exp_loop tmp1 in
	      let tmp3 = add_quantifiers [qvar] tmp2 in
	      ((push_exists [qvar] tmp3), flag)

  | Exists _ -> report_error no_pos ("Solver.elim_exists: Exists with an empty list of quantified variables")


(******************************************************************************************************************
														                                                           10.06.2008
														                                                           Utilities for simplifications:
														                                                           - whenever the pure part contains some arithmetic formula that can be further simplified --> call the theorem prover to perform the simplification
														                                                           Ex. x = 1 + 0 --> simplify to x = 1
******************************************************************************************************************)

and simpl_pure_formula (f : CP.formula) : CP.formula = match f with
  | CP.And (f1, f2, pos) -> CP.mkAnd (simpl_pure_formula f1) (simpl_pure_formula f2) pos
  | CP.Or (f1, f2, lbl, pos) -> CP.mkOr (simpl_pure_formula f1) (simpl_pure_formula f2) lbl pos
  | CP.Not (f1, lbl, pos) -> CP.mkNot (simpl_pure_formula f1) lbl pos
  | CP.Forall (sv, f1, lbl, pos) -> CP.mkForall [sv] (simpl_pure_formula f1) lbl pos
  | CP.Exists (sv, f1, lbl, pos) -> CP.mkExists [sv] (simpl_pure_formula f1) lbl pos
  | CP.BForm (f1,lbl) ->
        let simpl_f = CP.BForm(simpl_b_formula f1, lbl) in
	    (*let _ = print_string("\n[solver.ml]: Formula before simpl: " ^ Cprinter.string_of_pure_formula f ^ "\n") in
	      let _ = print_string("\n[solver.ml]: Formula after simpl: " ^ Cprinter.string_of_pure_formula simpl_f ^ "\n") in*)
	    simpl_f

and combine_struc (f1:struc_formula)(f2:struc_formula) :struc_formula = 
  let sat_subno = ref 0 in
  let rec combine_ext_struc (f1:ext_formula)(f2:ext_formula):ext_formula = match f1 with
    | ECase b -> let r = match f2 with
	    | ECase d ->
	          let comb = (List.fold_left (fun a1 (c11,c12)-> a1@(List.map (fun (c21,c22)-> 
				  ((Cpure.mkAnd c11 c21 d.formula_case_pos),c12,c22)) b.formula_case_branches) ) [] d.formula_case_branches) in
	          let comb = List.fold_left (fun a (c1,c2,c3)-> 
				  let sat = Tpdispatcher.is_sat_sub_no c1 sat_subno in
				  if sat then a
				  else (c1,(combine_struc c2 c3))::a)[] comb in
	          ECase {b with 
		          formula_case_exists = b.formula_case_exists@d.formula_case_exists;
		          formula_case_branches = comb}
	    | EBase d ->
	          ECase {b with formula_case_branches =  (List.map (fun (c1,c2)-> (c1,(combine_struc [f2] c2))) b.formula_case_branches)}
	    | EAssume _ -> ECase ({b with formula_case_branches = List.map (fun (c1,c2)-> (c1,(combine_struc c2 [f2])))
			      b.formula_case_branches})
		| EVariance e -> ECase {b with formula_case_branches =  (List.map (fun (c1,c2)-> (c1,(combine_struc [f2] c2))) b.formula_case_branches)}
	  in r	
    | EBase b -> let r = match f2 with
	    | ECase d ->
	          ECase {d with 	 formula_case_branches =  (List.map (fun (c1,c2)-> (c1,(combine_struc [f1] c2))) d.formula_case_branches)}
	    | EBase d -> EBase 
	          {
	              formula_ext_explicit_inst = b.formula_ext_explicit_inst @ d.formula_ext_explicit_inst;
	              formula_ext_implicit_inst = b.formula_ext_implicit_inst @ d.formula_ext_implicit_inst;
	              formula_ext_exists = b.formula_ext_exists @ d.formula_ext_exists;
	              formula_ext_base = normalize_combine b.formula_ext_base d.formula_ext_base b.formula_ext_pos ;
	              formula_ext_continuation = combine_struc b.formula_ext_continuation d.formula_ext_continuation;
	              formula_ext_pos = b.formula_ext_pos
	          }
	    | EAssume _ -> EBase ({b with formula_ext_continuation = combine_struc b.formula_ext_continuation [f2]})
		| EVariance _ -> EBase ({b with formula_ext_continuation = combine_struc b.formula_ext_continuation [f2]})
	  in r																												  
    | EAssume (x1,b, (y1',y2') )-> let r = match f2 with
	    | ECase d -> combine_ext_struc f2 f1
	    | EBase d -> combine_ext_struc f2 f1 
	    | EAssume (x2,d,(y1,y2)) -> EAssume ((x1@x2),(normalize_combine b d (Cformula.pos_of_formula d)),(y1,(y2^y2')))
		| EVariance e -> combine_ext_struc f2 f1
	  in r
	| EVariance e -> let r = match f2 with
		| ECase c -> ECase {c with formula_case_branches =  (List.map (fun (c1,c2)-> (c1,(combine_struc [f1] c2))) c.formula_case_branches)}
		| EBase _ -> EVariance ({e with formula_var_continuation = combine_struc e.formula_var_continuation [f2]})
		| EAssume _ -> EVariance ({e with formula_var_continuation = combine_struc e.formula_var_continuation [f2]})
		| EVariance e2 -> EVariance ({e with formula_var_measures = e.formula_var_measures@e2.formula_var_measures;
			  formula_var_escape_clauses = e.formula_var_escape_clauses@e2.formula_var_escape_clauses; (* [ec1,ec2] means ec1 or ec2 *)
			  formula_var_continuation = combine_struc e.formula_var_continuation e2.formula_var_continuation}) 
	  in r
  in
  List.fold_left (fun b c1->b@(List.map (fun c2->(combine_ext_struc c1 c2)) f2)) [] f1


and compose_struc_formula (delta : struc_formula) (phi : struc_formula) (x : CP.spec_var list) (pos : loc) =
  let rs = CP.fresh_spec_vars x in
  let rho1 = List.combine (List.map CP.to_unprimed x) rs in
  let rho2 = List.combine (List.map CP.to_primed x) rs in
  let new_delta = subst_struc rho2 delta in
  let new_phi = subst_struc rho1 phi in
  let new_f = combine_struc new_delta new_phi in
  let resform = push_struc_exists rs new_f in
  resform	
      
and transform_null (eqs) :(CP.b_formula list) = List.map (fun c-> match c with
  | Cpure.BVar _ 
  | Cpure.Lt _
  | Cpure.Lte _ -> c
  | Cpure.Eq (e1,e2,l) -> 
		if (Cpure.exp_is_object_var e1)&&(Cpure.is_num e2) then
		  if (Cpure.is_zero e2) then Cpure.Eq (e1,(Cpure.Null l),l)
		  else Cpure.Neq (e1,(Cpure.Null l),l)
		else if (Cpure.exp_is_object_var e2)&&(Cpure.is_num e1) then
		  if (Cpure.is_zero e1) then Cpure.Eq (e2,(Cpure.Null l),l)
		  else Cpure.Neq (e2,(Cpure.Null l),l)
		else c
  | Cpure.Neq (e1,e2,l)-> 
		if (Cpure.exp_is_object_var e1)&&(Cpure.is_num e2) then
		  if (Cpure.is_zero e2) then Cpure.Neq (e1,(Cpure.Null l),l)
		  else c
		else if (Cpure.exp_is_object_var e2)&&(Cpure.is_num e1) then
		  if (Cpure.is_zero e1) then Cpure.Neq (e2,(Cpure.Null l),l)
		  else c
		else c
  | _ -> c
) eqs
(*returns true if exists one unsat branch*)(*
and check_unsat_struc prog (cf:struc_formula):bool = 
		let rec inner (f:formula) (cf:struc_formula):bool =
			let rec helper (f:formula) (cf:ext_formula):bool = match cf with
			| EAssume b -> 
					 let pf, pfb = xpure prog f in
					(not(Tpdispatcher.is_sat pf false)) || (List.exists (fun (_,c2) -> not(Tpdispatcher.is_sat (Cpure.And (pf,c2,no_pos)) false)) pfb)
				| EBase b -> inner (normalize f b.formula_ext_base no_pos) b.formula_ext_continuation 
				| ECase b -> List.exists (fun (c1,c2)-> inner (normalize (formula_of_pure c1 no_pos) f no_pos) c2 ) b.formula_case_branches in	
		if (List.length cf)==0 then
			let pf, pfb = xpure prog f in
					(not(Tpdispatcher.is_sat pf false)) || (List.exists (fun (_,c2) -> not(Tpdispatcher.is_sat (Cpure.And (pf,c2,no_pos)) false)) pfb)
		else List.exists (helper f) cf in
	(*inner (mkTrue no_pos) cf*) false*)

let heap_entail_one_context_new (prog : prog_decl) (is_folding : bool)
       (b1:bool)  (ctx : context) 
    (conseq : formula) pos (b2:control_path_id): (list_context * proof) =
      heap_entail_one_context prog is_folding  ctx conseq pos

let heap_entail_struc_list_partial_context_init (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_partial_context)
        (conseq:struc_formula) pos (pid:control_path_id) : (list_partial_context * proof) = 
  let _ = set_entail_pos pos in
  Debug.devel_pprint ("heap_entail_init struc_list_partial_context_init:"
          ^ "\nconseq:"^ (Cprinter.string_of_struc_formula conseq) 
         ^ "\nctx:\n" ^ (Cprinter.string_of_list_partial_context cl)
  ^"\n") pos; 
  Gen.Profiling.push_time "entail_prune";
  let cl = normalize_frac_ctx_list prog (prune_ctx_list prog cl) in
(*  let _ = count_br_specialized prog cl in*)
  let conseq = normalize_frac_struc prog (prune_pred_struc prog false conseq) in
  Gen.Profiling.pop_time "entail_prune";
  heap_entail_prefix_init prog is_folding  has_post cl conseq pos pid (rename_labels_struc,Cprinter.string_of_struc_formula,(heap_entail_one_context_struc_nth "1"))

let heap_entail_struc_list_failesc_context_init (prog : prog_decl) (is_folding : bool)  (has_post: bool)
	(cl : list_failesc_context)(conseq:struc_formula) pos (pid:control_path_id) : (list_failesc_context * proof) = 
  let _ = set_entail_pos pos in
  Debug.devel_pprint ("heap_entail_init struc_list_failesc_context_init:"
          ^ "\nconseq:"^ (Cprinter.string_of_struc_formula conseq) 
         ^ "\nctx:\n" ^ (Cprinter.string_of_list_failesc_context cl)
  ^"\n") pos; 
  let res,prf = heap_entail_failesc_prefix_init prog is_folding  has_post cl conseq pos pid (rename_labels_struc,Cprinter.string_of_struc_formula,(heap_entail_one_context_struc_nth "2")) in
  ((* CF.list_failesc_context_simplify  *)res,prf)

let heap_entail_list_partial_context_init (prog : prog_decl) (is_folding : bool)  (cl : list_partial_context)
        (conseq:formula) pos (pid:control_path_id) : (list_partial_context * proof) = 
  let _ = set_entail_pos pos in
  Debug.devel_pprint ("heap_entail_init list_partial_context_init:"
          ^ "\nconseq:"^ (Cprinter.string_of_formula conseq) 
        ^ "\nctx:\n" ^ (Cprinter.string_of_list_partial_context cl)
  ^"\n") pos; 
  Gen.Profiling.push_time "entail_prune";  
  if cl==[] then ([],UnsatAnte)
  else begin
  let cl = reset_original_list_partial_context cl in
  let cl_after_prune = prune_ctx_list prog cl in
  let cl_after_prune = normalize_frac_ctx_list prog cl_after_prune in
  let conseq = prune_preds prog false conseq in
  let conseq = normalize_frac_formula prog conseq in
  Gen.Profiling.pop_time "entail_prune";
  let entail_fct = (fun c-> heap_entail_prefix_init prog is_folding  false c 
      conseq pos pid (rename_labels_formula ,Cprinter.string_of_formula,heap_entail_one_context_new)) in
  heap_entail_agressive_prunning entail_fct (*(prune_ctx_list prog)*) (fun a->a) (fun (c,_)-> isSuccessListPartialCtx c) cl_after_prune 
  end

let heap_entail_list_partial_context_init (prog : prog_decl) (is_folding : bool)  (cl : list_partial_context)
        (conseq:formula) pos (pid:control_path_id) : (list_partial_context * proof) = 
  let pr x = (string_of_int(List.length x))^"length" in
  Gen.Debug.loop_2_no "heap_entail_list_partial_context_init" pr (Cprinter.string_of_formula) (fun _ -> "?")
      (fun _ _ -> heap_entail_list_partial_context_init prog is_folding  cl conseq pos pid) cl conseq

let heap_entail_list_failesc_context_init (prog : prog_decl) (is_folding : bool)  (cl : list_failesc_context)
      (conseq:formula) pos (pid:control_path_id) : (list_failesc_context * proof) =
  let _ = set_entail_pos pos in
  Debug.devel_pprint ("heap_entail_init list_failesc_context_init:"
  ^ "\nconseq:"^ (Cprinter.string_of_formula conseq) 
  ^ "\nctx:\n" ^ (Cprinter.string_of_list_failesc_context cl)
  ^"\n") pos;
  if cl==[] then ([],UnsatAnte)
  else begin 
    Gen.Profiling.push_time "entail_prune";  
    let cl_after_prune = prune_ctx_failesc_list prog cl in
    let cl_after_prune = normalize_frac_ctx_failesc_list prog cl_after_prune in
    let conseq = prune_preds prog false conseq in
    let conseq = normalize_frac_formula prog conseq in
    Gen.Profiling.pop_time "entail_prune";
    heap_entail_failesc_prefix_init prog is_folding  false cl_after_prune conseq pos pid (rename_labels_formula ,Cprinter.string_of_formula,heap_entail_one_context_new)
  end
  