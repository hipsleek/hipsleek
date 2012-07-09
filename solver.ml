
(*
26.11.2008
todo: disable the default logging for omega
*)

open Globals
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Cast
open Cformula
open Prooftracer
open Gen.Basic
open Immutable
open Perm
open Mcpure_D
open Mcpure

module Inf = Infer
module CP = Cpure
module PR = Cprinter
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher

(** An Hoa : switch to do unfolding on duplicated pointers **)
let unfold_duplicated_pointers = ref false

(** An Hoa : to store the number of unfolding performed on duplicated pointers **)
let num_unfold_on_dup = ref 0

let simple_imply f1 f2 = let r,_,_ = TP.imply f1 f2 "simple_imply" false None in r   

let simple_imply f1 f2 =
  let pr = !CP.print_formula in
  Debug.no_2 "simple_imply" pr pr string_of_bool
  simple_imply f1 f2

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
  (*let f_fail e = e in*)
  let f_ctx e = 
    let f = e.es_formula in
    let _ = transform_formula (f_e_f,f_f,f_h_f,(f_memo,f_aset, f_formula, f_b_formula, f_exp)) f in
    Ctx e in
  let _ = transform_context f_ctx cl in
  ()

(*
  - count how many int constants are contained in one expression
  - if there are more than 1 --> means that we can simplify further (by performing the operation)
*)

let rec count_iconst (f : CP.exp) = match f with
  | CP.Subtract (e1, e2, _)
  | CP.Add (e1, e2, _) -> ((count_iconst e1) + (count_iconst e2))
  | CP.Mult (e1, e2, _)
  | CP.Div (e1, e2, _) -> ((count_iconst e1) + (count_iconst e2))
  | CP.IConst _ -> 1
  | _ -> 0

let simpl_b_formula (f : CP.b_formula): CP.b_formula =
  let (pf,il) = f in
  match pf with
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
  	        | CP.BForm(simpl_f1, _) ->
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
      let fv = (h_fv b.formula_base_heap)@(mfv b.formula_base_pure) in
      let nmem = filter_useless_memo_pure (TP.simplify_a 5) simp_b fv b.formula_base_pure in
      Base {b with formula_base_pure = nmem;}
    | Exists e-> 
      let fv = (h_fv e.formula_exists_heap)@(mfv e.formula_exists_pure)@e.formula_exists_qvars in
      let nmem = filter_useless_memo_pure (TP.simplify_a 4) simp_b fv e.formula_exists_pure in
      Exists {e with formula_exists_pure = nmem;}

let filter_formula_memo f (simp_b:bool) =
  let pr = Cprinter.string_of_formula in 
  Debug.no_2 "filter_formula_memo"  
    pr string_of_bool pr 
    (fun _ _ -> filter_formula_memo f simp_b) f simp_b

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
		if (List.length need_prunning)<=0 then (true,None) (* *)
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
            let wrap_f (c,_) = CP.BForm ((memo_f_neg c),None) in
            let ll = List.map (fun l -> List.fold_left (fun a c-> CP.mkOr a (wrap_f c) None no_pos) (wrap_f (List.hd l)) (List.tl l)) ll in
            let inst_forms = CP.conj_of_list ll no_pos in
            (*let inst_forms = CP.conj_of_list (List.map (fun (c,_)-> CP.BForm ((memo_f_neg c),None)) new_cond) no_pos in*)
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
  let pr2 (c,d)= Cprinter.pr_pair_aux string_of_bool (Cprinter.pr_opt pr1) in
  let pr = Cprinter.string_of_h_formula in
  Debug.no_2 "pr_branches_subsume " pr pr pr2 (fun _ _ -> prune_branches_subsume_x prog lhs_node rhs_node) lhs_node rhs_node

(*LDK: only use crt_heap_entailer
a : Cformula.list_failesc_context
*)  
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
  
(* let clear_entailment_history_es (es :entail_state) :context =  *)
(*   Ctx {(empty_es (mkTrueFlow ()) no_pos) with  *)
(*     es_formula = filter_formula_memo es.es_formula false; *)
(* 	es_path_label = es.es_path_label; *)
(* 	es_prior_steps= es.es_prior_steps; *)
(* 	es_var_measures = es.es_var_measures; *)
(* 	es_var_label = es.es_var_label; *)
(*     es_infer_vars = es.es_infer_vars; *)
(* 	es_var_ctx_lhs = es.es_var_ctx_lhs(\*; *)
(* 	es_var_ctx_rhs = es.es_var_ctx_rhs; *)
(* 	es_var_subst = es.es_var_subst*\) *)
(*   }  *)


(* let clear_entailment_history xp (ctx : context) : context =   *)
(*   transform_context (clear_entailment_history_es xp) ctx *)

(* let clear_entailment_history_list xp (ctx : list_context) : list_context =  *)
(*   transform_list_context (clear_entailment_history_es xp,(fun c->c)) ctx  *)

(* let clear_entailment_history_partial_list xp (ctx : list_partial_context) : list_partial_context =  *)
(*   transform_list_partial_context (clear_entailment_history_es xp,(fun c->c)) ctx  *)

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
      | Base ({formula_base_heap = h;
	    formula_base_pure = p;
	    formula_base_branches = br;
	    formula_base_pos = pos}) -> 
	        h_formula_2_mem h [] prog
      | Exists ({formula_exists_qvars = qvars;
	    formula_exists_heap = qh;
	    formula_exists_pure = qp;
	    formula_exists_branches = br;
	    formula_exists_pos = pos}) ->
	        h_formula_2_mem qh qvars prog
      | Or ({formula_or_f1 = f1;
	    formula_or_f2 = f2;
	    formula_or_pos = pos}) ->
	        let m1 = helper f1  in
	        let m2 = helper f2  in 
	        {mem_formula_mset = (CP.DisjSetSV.or_disj_set m1.mem_formula_mset m2.mem_formula_mset)}
  in helper f

and formula_2_mem (f : formula) prog : CF.mem_formula = 
  Debug.no_1 "formula_2_mem" Cprinter.string_of_formula Cprinter.string_of_mem_formula
      (fun _ -> formula_2_mem_x f prog) f

and h_formula_2_mem_debug (f : h_formula) (evars : CP.spec_var list) prog : CF.mem_formula = 
  Debug.no_1 "h_formula_2_mem" Cprinter.string_of_h_formula Cprinter.string_of_mem_formula
      (fun f -> h_formula_2_mem f evars prog) f

and h_formula_2_mem (f : h_formula) (evars : CP.spec_var list) prog : CF.mem_formula =
  Debug.no_2 "h_formula_2_mem"  Cprinter.string_of_h_formula Cprinter.string_of_spec_var_list Cprinter.string_of_mem_formula (fun f evars -> h_formula_2_mem_x f evars prog) f evars

and h_formula_2_mem_x (f : h_formula) (evars : CP.spec_var list) prog : CF.mem_formula = 
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
	        let m1 = helper h1  in
	        let m2 = helper h2 in
	        let m = (CP.DisjSetSV.merge_disj_set m1.mem_formula_mset m2.mem_formula_mset) in
	        {mem_formula_mset = m;}
      | DataNode ({h_formula_data_node = p;
	    h_formula_data_pos = pos}) ->
	        let new_mset = 
	          if List.mem p evars then CP.DisjSetSV.mkEmpty
	          else CP.DisjSetSV.singleton_dset (p(*, CP.mkTrue pos*)) in
	        {mem_formula_mset = new_mset;}
      | ViewNode ({ h_formula_view_node = p;
        h_formula_view_name = c;
        h_formula_view_arguments = vs;
        h_formula_view_remaining_branches = lbl_lst;
        h_formula_view_pos = pos}) ->
            let ba = look_up_view_baga prog c p vs in
            let vdef = look_up_view_def pos prog.prog_view_decls c in
            let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
            let to_svs = p :: vs in
 	        let new_mset = 
              (match lbl_lst with
                |None ->
                      if List.mem p evars then CP.BagaSV.mkEmpty
	                    else ba 
                | Some ls -> 
                   lookup_view_baga_with_subs ls vdef from_svs to_svs) in
	        {mem_formula_mset = CP.DisjSetSV.one_list_dset new_mset;} 
      | Hole _
      | HTrue
      | HFalse ->
         (*  let _ = print_endline "h_formula_2_mem: HTrue, HFalse, Hole" in*)
         {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
  in helper f
  
let rec xpure (prog : prog_decl) (f0 : formula) : (mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) =
  Debug.no_1 "xpure"
	  Cprinter.string_of_formula
	  (fun (r1, _, _, r4) ->
	      (Cprinter.string_of_mix_formula r1) ^ "#" ^ (Cprinter.string_of_mem_formula r4))
	  (fun f0 -> xpure_x prog f0) f0
      
and xpure_x (prog : prog_decl) (f0 : formula) : (mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) =
  (* print_string "calling xpure"; *)
  if (!Globals.allow_imm) then xpure_symbolic prog f0
  else
    let a, b, c = xpure_mem_enum prog f0 in
    (a, b, [], c)

(* and xpure (prog : prog_decl) (f0 : formula) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) = *)

(*   let pr (m,_,_,_) = Cprinter.string_of_mix_formula m in *)
(*   Debug.no_1 "xpure"  *)
(*       Cprinter.string_of_formula pr *)
(*       (fun _ -> xpure_x prog f0) f0 *)

and xpure_heap i (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula)
      (*= Debug.no_2_num i "xpure_heap" Cprinter.string_of_h_formula string_of_int (fun (mf,_,_,m) -> pr_pair Cprinter.string_of_mix_formula Cprinter.string_of_mem_formula (mf,m)) *)
      = Debug.no_2_num i "xpure_heap" Cprinter.string_of_h_formula string_of_int (fun (mf,_,svl,m) -> pr_triple Cprinter.string_of_mix_formula Cprinter.string_of_spec_var_list Cprinter.string_of_mem_formula (mf,svl,m)) 
  (fun _ _ -> xpure_heap_x prog h0 which_xpure) h0 which_xpure

and xpure_heap_x (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) =
  if (!Globals.allow_imm) then 
    if (Perm.allow_perm ()) then 
      xpure_heap_symbolic_perm prog h0 which_xpure
    else
      xpure_heap_symbolic prog h0 which_xpure
  else
    if (Perm.allow_perm ()) then 
      let a, b, c = xpure_heap_perm prog h0 which_xpure in
      (a, b, [], c)
    else
      let a, b, c = xpure_heap_mem_enum prog h0 which_xpure in
      (a, b, [], c)

(* TODO : if no complex & --eps then then return true else xpure1 generated;
   what if user invariant has a disjunct? *)

and xpure_mem_enum (prog : prog_decl) (f0 : formula) : (mix_formula * (branch_label * CP.formula) list * CF.mem_formula) = 
  Debug.no_1 "xpure_mem_enum" Cprinter.string_of_formula (fun (a1,_,a3)->(Cprinter.string_of_mix_formula a1)^"#"
      ^(Cprinter.string_of_mem_formula a3)) (fun f0 -> xpure_mem_enum_x prog f0) f0

(* xpure approximation with memory enumeration *)
and xpure_mem_enum_x (prog : prog_decl) (f0 : formula) : (mix_formula * (branch_label * CP.formula) list * CF.mem_formula) = 
  (*use different xpure functions*)
  (* let xpure_h = if (Perm.allow_perm ()) then xpure_heap_perm else xpure_heap_mem_enum in *)
  let mset = formula_2_mem f0 prog in 
  let rec xpure_helper  (prog : prog_decl) (f0 : formula) : (mix_formula * (branch_label * CP.formula) list) = 
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
	        (mkOr_mems pf1 pf2 ), br

      | Base ({ formula_base_heap = h;
		formula_base_pure = p;
		formula_base_branches = br;
		formula_base_pos = pos}) ->
            let (ph, phb, _) = xpure_heap_mem_enum prog h 1 in
            (*let (ph, phb, _) = xpure_h prog h 1 in*)
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
		formula_exists_pos = pos}) ->
            let (pqh, pqhb, _) = xpure_heap_mem_enum prog qh 1 in
            (*let (pqh, pqhb, _) = xpure_h prog qh 1 in*)
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


and xpure_heap_mem_enum(*_debug*) (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list * CF.mem_formula) =  
  Debug.no_2 "xpure_heap_mem_enum" Cprinter.string_of_h_formula string_of_int (fun (a1,_,a3)->(Cprinter.string_of_mix_formula a1)^"#"
    ^(Cprinter.string_of_mem_formula a3)) (fun _ _ -> xpure_heap_mem_enum_x prog h0 which_xpure) h0 which_xpure 

and xpure_heap_mem_enum_x (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list * CF.mem_formula) =
  (* let _  = print_string("Calling xpure_heap for f = " ^ (Cprinter.string_of_h_formula h0) ^ "\n") in *)
  let memset = h_formula_2_mem h0 [] prog in
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

(* Return a CF.formula instead of a flatten MCP formula, the heap parts is not complex *)	
and xpure_symbolic_slicing (prog : prog_decl) (f0 : formula) : (formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) =
  let mset = formula_2_mem f0 prog in 
  let rec xpure_symbolic_helper (prog : prog_decl) (f0 : formula) : (formula * (branch_label * CP.formula) list * CP.spec_var list) =
	match f0 with
      | Or ({ formula_or_f1 = f1;
	    formula_or_f2 = f2;
		formula_or_pos = pos }) ->
            let ipf1, pf1b, avars1 = xpure_symbolic_helper prog f1 in
            let ipf2, pf2b, avars2 = xpure_symbolic_helper prog f2 in
            let br = CP.or_branches pf1b pf2b in
	        let res_form = mkOr ipf1 ipf2 pos in
            (res_form, br, (avars1 @ avars2))
      | Base b ->
	        let ({ formula_base_heap = h;
	        formula_base_pure = p;
			formula_base_branches = fbr;
			formula_base_pos = pos }) = b in
            let ph, br, addrs, _ = xpure_heap_symbolic prog h 1 in
            let n_p = MCP.merge_mems p ph true in
            let cf = (MCP.fold_mem_lst (CP.mkTrue no_pos) false true n_p) in
            let rb = CP.merge_branches_with_common br fbr cf [] in   
            (*let n_f0 = Base { b with formula_base_pure = n_p } in*)
	        (* Set a complex heap formula to a simpler one *)
	        let n_f0 = mkBase HTrue n_p TypeTrue (mkTrueFlow ()) [] pos in (* formula_of_mix_formula n_p *)
            (n_f0, rb, addrs)
      | Exists e ->
	        let ({ formula_exists_qvars = qvars;
			formula_exists_heap = qh;
			formula_exists_pure = qp;
			formula_exists_branches = fbr;
			formula_exists_pos = pos}) = e in 
            let pqh, br, addrs', _ = xpure_heap_symbolic prog qh 1 in
            let sqvars = (* List.map CP.to_int_var *) qvars in
            let addrs = Gen.BList.difference_eq CP.eq_spec_var addrs' sqvars in

            let n_qp = MCP.merge_mems qp pqh true in
            (*let res_form = MCP.memo_arith_simplify (MCP.memo_pure_push_exists sqvars tmp1) in
	          let n_f0 = mkBase HTrue res_form TypeTrue (mkTrueFlow ()) [] pos in*)
            (* Set a complex heap formula to a simpler one *)
	        let n_f0 = mkExists qvars HTrue n_qp TypeTrue (mkTrueFlow ()) [] pos in
	        
            let cf = (MCP.fold_mem_lst (CP.mkTrue no_pos) false true n_qp) in

            let rb = CP.merge_branches_with_common br fbr cf sqvars in   
            (n_f0, rb, addrs)
  in
  let pf, pb, pa = xpure_symbolic_helper prog f0 in
  (pf, pb, pa, mset)

(* xpure heap in the presence of permissions *)
(* similar to xpure_heap_mem_enum *)
(* but use permission invariants instead of baga *)
and xpure_heap_perm (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list * CF.mem_formula) =  Debug.no_2 "xpure_heap_perm" Cprinter.string_of_h_formula string_of_int (fun (a1,_,a3)->(Cprinter.string_of_mix_formula a1)^"#"
    ^(Cprinter.string_of_mem_formula a3)) (fun _ _ -> xpure_heap_perm_x prog h0 which_xpure) h0 which_xpure 

and xpure_heap_perm_x (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list * CF.mem_formula) =
  (* let _  = print_string("Calling xpure_heap_perm for f = " ^ (Cprinter.string_of_h_formula h0) ^ "\n") in *)
  let memset = h_formula_2_mem h0 [] prog in

  let rec xpure_heap_helper (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list) = 
    match h0 with
      | DataNode ({h_formula_data_node = p;
        h_formula_data_perm = frac;
		h_formula_data_pos = pos}) ->
            (* let i = fresh_int2 () in *)
            (*LDK: not check for alias*)
            (* let non_null = CP.mkTrue pos in *)
            let non_null = CP.mkNeqNull p pos in
            (* let non_null = CP.mkEqVarInt p i pos in *)
            (*LDK: add fractional invariant 0<f<=1, if applicable*)
            (match frac with
              | None ->
	                (MCP.memoise_add_pure_N (MCP.mkMTrue pos) non_null , [])
              | Some f ->
                    let frac_inv = mkPermInv f in
                    let res = CP.mkAnd non_null frac_inv no_pos in
	                (MCP.memoise_add_pure_N (MCP.mkMTrue pos) res , [])
            )

	  (* (MCP.memoise_add_pure_N (MCP.mkMTrue pos) non_null , []) *)
      | ViewNode ({ h_formula_view_node = p;
		h_formula_view_name = c;
		h_formula_view_perm = frac; (*Viewnode does not neccessary have invariant on fractional permission*)
		h_formula_view_arguments = vs;
		h_formula_view_remaining_branches = rm_br;
		h_formula_view_pos = pos}) ->
            let vdef = look_up_view_def pos prog.prog_view_decls c in
            (*LDK: ??? this helper seems not do any thing. Temporary disable it*)
            (* let rec helper addrs = *)
	        (*   match addrs with *)
	        (*     | a :: rest -> *)
	        (*           let i = fresh_int () in *)
	        (*           let non_null = CP.mkEqVarInt a i pos in *)
	        (*           let rest_f = helper rest in *)
	        (*           let res_form = CP.mkAnd non_null rest_f pos in *)
	        (*           res_form *)
	        (*     | [] -> CP.mkTrue pos in *)

            (*LDK: add fractional invariant 0<f<=1, if applicable*)
            let frac_inv =
              (match frac with
                | None ->
	                  CP.mkTrue pos
                | Some f ->
                      mkPermInv f
              ) in
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
              | None -> 
	                (MCP.memoise_add_pure_N (MCP.mkMTrue pos) frac_inv , [])

              (* (MCP.mkMTrue no_pos, []) *)
              | Some xp1 ->
                    let vinv = match which_xpure with
                      | -1 -> (MCP.mkMTrue no_pos, [])
                      | 0 -> vdef.view_user_inv
                      | _ -> xp1 in

                    (*LDK: ??? be careful to handle frac var properly. 
                      Currently, no fracvar in view definition*)
                    let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
                    let to_svs = p :: vs in
                    let (f, b) = vinv in

                    (*add fractional invariant*)
                    let frac_inv_mix = MCP.OnePF frac_inv in
                    let f = CF.add_mix_formula_to_mix_formula frac_inv_mix f in

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
  (ph, pb,  memset)
      (* (\*LDK: temporary disable UNSAT BAGA check*\) *)
      (* if (is_sat_mem_formula memset) then  *)
      (*   (ph, pb,  memset) *)
      (* else (MCP.mkMFalse no_pos, pb, memset)   *)

and xpure_symbolic (prog : prog_decl) (h0 : formula) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) = 
  Debug.no_1 "xpure_symbolic" Cprinter.string_of_formula 
      (fun (p1,_,vl,p4) -> (Cprinter.string_of_mix_formula p1)^"#"^(Cprinter.string_of_spec_var_list vl)^"#
"^(Cprinter.string_of_mem_formula p4)) (* (fun (p1,_,_,p4) -> not(is_sat_mem_formula p4)) *)
      (fun h0 -> xpure_symbolic_orig prog h0) h0
	  
(* xpure approximation without memory enumeration *)
and xpure_symbolic_orig (prog : prog_decl) (f0 : formula) : 
      (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) =
  (*use different xpure functions*)
  let xpure_h = if (Perm.allow_perm ()) then xpure_heap_symbolic_perm else xpure_heap_symbolic in
  let mset = formula_2_mem f0 prog in 
  let rec xpure_symbolic_helper (prog : prog_decl) (f0 : formula) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list) = match f0 with
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
          (res_form, br, (avars1 @ avars2))
    | Base ({ formula_base_heap = h;
	  formula_base_pure = p;
	  formula_base_branches = fbr;
	  formula_base_pos = pos}) ->
          let ph, br, addrs, _ = xpure_heap_symbolic prog h 1 in
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
	  formula_exists_pos = pos}) ->
          let pqh, br, addrs', _ = xpure_h prog qh 1 in
          let sqvars = (* List.map CP.to_int_var *) qvars in
          let addrs = Gen.BList.difference_eq CP.eq_spec_var addrs' sqvars in

		  (*let _ = print_string ("\nxpure_symbolic: qp: " ^ (Cprinter.string_of_mix_formula qp) ^ "\n") in
		    let _ = print_string ("\nxpure_symbolic: pqh: " ^ (Cprinter.string_of_mix_formula pqh) ^ "\n") in*)
		  
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

and xpure_heap_symbolic (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) = 
  (*Debug.no_1_opt 
    (fun (p1,_,_,p4) -> not(is_sat_mem_formula p4)) 
    "xpure_heap_symbolic" Cprinter.string_of_h_formula 
    (fun (p1,_,p3,p4) -> (Cprinter.string_of_mix_formula p1)^"#"^(string_of_spec_var_list p3)^"#"^(Cprinter.string_of_mem_formula p4)
    ^string_of_bool(is_sat_mem_formula p4)) 
    (fun h0 -> xpure_heap_symbolic_x prog h0 which_xpure) h0*)
  Debug.no_1 
      "xpure_heap_symbolic" Cprinter.string_of_h_formula 
      (fun (p1,_,p3,p4) -> (Cprinter.string_of_mix_formula p1)^"#"^(string_of_spec_var_list p3)^"#"^(Cprinter.string_of_mem_formula p4)
          ^string_of_bool(is_sat_mem_formula p4)) 
      (fun h0 -> xpure_heap_symbolic_x prog h0 which_xpure) h0

and xpure_heap_symbolic_x (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) = 
  let memset = h_formula_2_mem h0 [] prog in
  let ph, pb, pa = xpure_heap_symbolic_i prog h0 which_xpure in
  if (is_sat_mem_formula memset) then 
    (ph, pb, pa, memset)
  else (MCP.mkMFalse no_pos, pb, pa, memset)  

(* xpure heap symbolic in the presence of permissions *)
(* similar to xpure_heap_symbolic *)
and xpure_heap_symbolic_perm (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) = 
  Debug.no_1 
      "xpure_heap_symbolic_perm" Cprinter.string_of_h_formula 
      (fun (p1,_,p3,p4) -> (Cprinter.string_of_mix_formula p1)^"#"^(string_of_spec_var_list p3)^"#"^(Cprinter.string_of_mem_formula p4)
          ^string_of_bool(is_sat_mem_formula p4)) 
      (fun h0 -> xpure_heap_symbolic_perm_x prog h0 which_xpure) h0

(*xpure heap in the presence of imm and permissions*)
and xpure_heap_symbolic_perm_x (prog : prog_decl) (h0 : h_formula) (which_xpure :int) : (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list * CF.mem_formula) = 
  let memset = h_formula_2_mem h0 [] prog in
  let ph, pb, pa = xpure_heap_symbolic_perm_i prog h0 which_xpure in
  (* (ph, pb, pa, memset) *)
  (*TO CHECK: temporarily disable is_sat*)
  if (is_sat_mem_formula memset) then
    (ph, pb, pa, memset)
  else (MCP.mkMFalse no_pos, pb, pa, memset)

and heap_baga (prog : prog_decl) (h0 : h_formula): CP.spec_var list = 
  let rec helper h0 = match h0 with
    | DataNode ({ h_formula_data_node = p;}) ->[p]
    | ViewNode ({ h_formula_view_node = p;
      h_formula_view_name = c;
      h_formula_view_arguments = vs;
      h_formula_view_remaining_branches = lbl_lst;
      h_formula_view_pos = pos}) ->
          (match lbl_lst with
            | None -> look_up_view_baga prog c p vs
            | Some ls ->  
                  let vdef = look_up_view_def pos prog.prog_view_decls c in
                  let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
                  let to_svs = p :: vs in
                  lookup_view_baga_with_subs ls vdef from_svs to_svs )
    | Star ({ h_formula_star_h1 = h1;h_formula_star_h2 = h2})
    | Phase ({ h_formula_phase_rd = h1;h_formula_phase_rw = h2;}) 
    | Conj ({ h_formula_conj_h1 = h1;h_formula_conj_h2 = h2;}) -> (helper h1) @ (helper h2)
    | HTrue | Hole _ | HFalse -> [] in
  helper h0

and xpure_heap_symbolic_i (prog : prog_decl) (h0 : h_formula) i: (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list) = 
  let pr (mf,bl,_) = pr_pair Cprinter.string_of_mix_formula (pr_list (fun (_,f) -> Cprinter.string_of_pure_formula f)) (mf,bl) in
  Debug.no_1 "xpure_heap_symbolic_i" Cprinter.string_of_h_formula pr
      (fun h0 -> xpure_heap_symbolic_i_x prog h0 i) h0

and xpure_heap_symbolic_i_x (prog : prog_decl) (h0 : h_formula) xp_no: (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list) = 
  let rec helper h0 = match h0 with
    | DataNode ({ h_formula_data_node = p;
	  h_formula_data_label = lbl;
	  h_formula_data_pos = pos}) ->
          let non_zero = CP.BForm ((CP.Neq (CP.Var (p, pos), CP.Null pos, pos), None), lbl) in
          (MCP.memoise_add_pure_N (MCP.mkMTrue pos) non_zero , [], [p])
    | ViewNode ({ h_formula_view_node = p;
	  h_formula_view_name = c;
	  h_formula_view_arguments = vs;
	  h_formula_view_remaining_branches = lbl_lst;
	  h_formula_view_pos = pos}) ->
          (* let _ = print_endline ("xpure_heap_symbolic_i: ViewNode") in*)
          let ba = look_up_view_baga prog c p vs in
          let vdef = look_up_view_def pos prog.prog_view_decls c in
          let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
          let to_svs = p :: vs in
          (*print_string ("from svs: "^(pr_list Cprinter.string_of_spec_var from_svs)^"\n");
            print_string ("to svs: "^(pr_list Cprinter.string_of_spec_var to_svs)^"\n");*)
          (match lbl_lst with
            | None -> 
                  (*print_string ("name: "^(vdef.view_name)^"\n") ;*)
                  let vinv, vinv_b = if (xp_no=1) then vdef.view_x_formula else vdef.view_user_inv in
                  (*print_string ("vinv1: "^(Cprinter.string_of_mix_formula vinv)^"\n");*)
                  (*let from_addrs = vdef.view_addr_vars in
                    print_string ("from vars: "^(pr_list Cprinter.string_of_spec_var from_addrs)^"\n");
                    let to_addrs = CP.fresh_spec_vars from_addrs in*)
                  let subst_m_fun f =
                    let tmp1 = MCP.subst_avoid_capture_memo(*_debug2*) from_svs to_svs f in
                    (*MCP.memo_subst (List.combine from_addrs to_addrs)*) tmp1 (* no capture can happen *) in
                  let subst_fun f =
                    let tmp1 = CP.subst_avoid_capture from_svs to_svs f in
                    (*CP.subst (List.combine from_addrs to_addrs)*) tmp1 (* no capture can happen *) in
                    (* let _ = print_endline ("xpure_heap_symbolic_i NONE: svl = " ^ (Cprinter.string_of_spec_var_list ba)) in *)
                    (*let svinv = subst_m_fun vinv in*)
                    (*print_string ("vinv2: "^(Cprinter.string_of_mix_formula svinv)^"\n");*)
                  (subst_m_fun vinv, List.map (fun (l,x) -> (l, subst_fun x)) vinv_b, ba (*to_addrs*)) 
            | Some ls ->  
                  let ba = lookup_view_baga_with_subs ls vdef from_svs to_svs in
			      (* let _ = print_endline ("xpure_heap_symbolic_i SOME: svl = " ^ (Cprinter.string_of_spec_var_list ba)) in*)
                  (MCP.mkMTrue no_pos, [], ba))
    | Star ({ h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
          (* let _ = print_endline ("xpure_heap_symbolic_i: Star") in*)
          let ph1, b1, addrs1 = helper h1 in
          let ph2, b2, addrs2 = helper h2 in
          (* let all_diff = *)
          (* 	if !no_diff then P.mkTrue no_pos *)
          (* 	else pairwise_diff addrs1 addrs2 pos in *)
          let tmp1 = MCP.merge_mems ph1 ph2 true in
          (* let res_form = MCP.memoise_add_pure_N tmp1 all_diff in *)
          (tmp1, CP.merge_branches b1 b2, addrs1 @ addrs2)
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
          let tmp1 = merge_mems ph1 ph2 true in
          (*let res_form = memoise_add_pure_N tmp1 all_diff in*)
          (tmp1, CP.merge_branches b1 b2, addrs1 @ addrs2)	      
    | HTrue -> (mkMTrue no_pos, [], [])
    | Hole _ -> (mkMTrue no_pos, [], []) (* shouldn't get here *)
    | HFalse -> (mkMFalse no_pos, [], []) in
  helper h0

(*xpure heap in the presence of imm and permissions*)
and xpure_heap_symbolic_perm_i (prog : prog_decl) (h0 : h_formula) i: (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list) = 
  let pr (mf,bl,_) = pr_pair Cprinter.string_of_mix_formula (pr_list (fun (_,f) -> Cprinter.string_of_pure_formula f)) (mf,bl) in
  Debug.no_1 "xpure_heap_symbolic_perm_i" Cprinter.string_of_h_formula pr
      (fun h0 -> xpure_heap_symbolic_perm_i_x prog h0 i) h0

and xpure_heap_symbolic_perm_i_x (prog : prog_decl) (h0 : h_formula) xp_no: (MCP.mix_formula * (branch_label * CP.formula) list * CP.spec_var list) = 
  let rec helper h0 = match h0 with
    | DataNode ({ h_formula_data_node = p;
      h_formula_data_perm = frac;
	  h_formula_data_label = lbl;
	  h_formula_data_pos = pos}) ->
          let non_zero = CP.BForm ( (CP.Neq (CP.Var (p, pos), CP.Null pos, pos), None),lbl) in
          (*LDK: add fractional invariant 0<f<=1, if applicable*)
          (match frac with
            | None ->
	              (MCP.memoise_add_pure_N (MCP.mkMTrue pos) non_zero , [],[p])
            | Some f ->
                  let frac_inv = mkPermInv f in
                  let res = CP.mkAnd non_zero frac_inv no_pos in
	              (MCP.memoise_add_pure_N (MCP.mkMTrue pos) res , [], [p])
          )
              (* | DataNode ({ h_formula_data_node = p; *)
	          (*   h_formula_data_label = lbl; *)
	          (*   h_formula_data_pos = pos}) -> *)
              (*       let non_zero = CP.BForm ((CP.Neq (CP.Var (p, pos), CP.Null pos, pos), None),lbl) in *)
              (*       (MCP.memoise_add_pure_N (MCP.mkMTrue pos) non_zero , [], [p]) *)
    | ViewNode ({ h_formula_view_node = p;
	  h_formula_view_name = c;
	  h_formula_view_perm = frac; (*Viewnode does not neccessary have invariant on fractional permission*)
	  h_formula_view_arguments = vs;
	  h_formula_view_remaining_branches = lbl_lst;
	  h_formula_view_pos = pos}) ->
          (* let _ = print_endline ("xpure_heap_symbolic_i: ViewNode") in*)
          let ba = look_up_view_baga prog c p vs in
          let vdef = look_up_view_def pos prog.prog_view_decls c in
          let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
          let to_svs = p :: vs in
          (*print_string ("from svs: "^(pr_list Cprinter.string_of_spec_var from_svs)^"\n");
            print_string ("to svs: "^(pr_list Cprinter.string_of_spec_var to_svs)^"\n");*)
          (match lbl_lst with
            | None -> (*--imm only*)
                  (*LDK: add fractional invariant 0<f<=1, if applicable*)
                  let frac_inv =
                    (match frac with
                      | None ->
	                        CP.mkTrue pos
                      | Some f ->
                            mkPermInv f
                    ) in
                  let vinv, vinv_b = if (xp_no=1) then vdef.view_x_formula else vdef.view_user_inv in
                  (*add fractional invariant*)
                  let frac_inv_mix = MCP.OnePF frac_inv in
                  let vinv = CF.add_mix_formula_to_mix_formula frac_inv_mix vinv in


                  (*let from_addrs = vdef.view_addr_vars in*)
                  (* let to_addrs = CP.fresh_spec_vars from_addrs in *)
                  let subst_m_fun f =
                    let tmp1 = MCP.subst_avoid_capture_memo(*_debug2*) from_svs to_svs f in
                    (*MCP.memo_subst (List.combine from_addrs to_addrs)*) tmp1 (* no capture can happen *) in
                  let subst_fun f =
                    let tmp1 = CP.subst_avoid_capture from_svs to_svs f in
                    (*CP.subst (List.combine from_addrs to_addrs)*) tmp1 (* no capture can happen *) in
                    (* let _ = print_endline ("xpure_heap_symbolic_i NONE: svl = " ^ (Cprinter.string_of_spec_var_list ba)) in *)
                    (*let svinv = subst_m_fun vinv in*)
                    (*print_string ("vinv2: "^(Cprinter.string_of_mix_formula svinv)^"\n");*)
                  (subst_m_fun vinv, List.map (fun (l,x) -> (l, subst_fun x)) vinv_b, ba (*to_addrs*)) 
            | Some ls ->(*--imm and --eps *)
                  (*??? what is it*)
                  let ba = lookup_view_baga_with_subs ls vdef from_svs to_svs in
			      (* let _ = print_endline ("xpure_heap_symbolic_i SOME: svl = " ^ (Cprinter.string_of_spec_var_list ba)) in*)
                  (MCP.mkMTrue no_pos, [], ba))
    | Star ({ h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) ->
          (* let _ = print_endline ("xpure_heap_symbolic_i: Star") in*)
          let ph1, b1, addrs1 = helper h1 in
          let ph2, b2, addrs2 = helper h2 in
          (* let all_diff = *)
          (* 	if !no_diff then P.mkTrue no_pos *)
          (* 	else pairwise_diff addrs1 addrs2 pos in *)
          let tmp1 = MCP.merge_mems ph1 ph2 true in
          (* let res_form = MCP.memoise_add_pure_N tmp1 all_diff in *)
          (tmp1, CP.merge_branches b1 b2, addrs1 @ addrs2)
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
          (tmp1, CP.merge_branches b1 b2, addrs1 @ addrs2)	      
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

and prune_branch_ctx prog (pt,bctx) = 
  let r = prune_ctx prog bctx in
  let _ = count_br_specialized prog r in
  (pt,r)   

and prune_list_ctx prog ctx = match ctx with
  | SuccCtx c -> SuccCtx (List.map (prune_ctx prog) c)
  | _ -> ctx

and prune_ctx_list prog ctx = List.map (fun (c1,c2)->(c1,List.map (prune_branch_ctx prog) c2)) ctx

and prune_ctx_failesc_list prog ctx = List.map (fun (c1,c2,c3)-> 
    let rc3 = List.map (prune_branch_ctx prog) c3 in
    (c1,c2,rc3))  ctx

and prune_pred_struc prog (simp_b:bool) f = 
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_2 "prune_pred_struc" pr string_of_bool pr (fun _ _ -> prune_pred_struc_x prog simp_b f) f simp_b

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
        (*| EVariance b -> EVariance {b with
            formula_var_continuation = helper b.formula_var_continuation}*)
        | EInfer b -> EInfer {b with 
              formula_inf_continuation = helper b.formula_inf_continuation}
  in    
  (*let _ = print_string ("prunning: "^(Cprinter.string_of_struc_formula f)^"\n") in*)
  List.map helper f

and prune_preds_x prog (simp_b:bool) (f:formula):formula =   
  let imply_w f1 f2 = let r,_,_ = TP.imply f1 f2 "elim_rc" false None in r in   
  let f_p_simp c = if simp_b then MCP.elim_redundant(*_debug*) (imply_w,TP.simplify_a 3) c else c in
  let rec fct i op oh = if (i== !Globals.prune_cnt_limit) then (op,oh)
  else
    let nh, mem, changed = heap_prune_preds_mix prog oh op in 
    if changed then fct (i+1) mem nh
    else ((match op with | MCP.MemoF f -> MCP.MemoF (MCP.reset_changed f)| _ -> op) ,oh) in
  let rec helper_formulas f = match f with
    | Or o -> 
          let f1 = helper_formulas o.formula_or_f1 in
          let f2 = helper_formulas o.formula_or_f2 in
          mkOr f1 f2 o.formula_or_pos
              (*Or {o with formula_or_f1 = f1; formula_or_f2 = f2;}*)
    | Exists e ->    
          let rp,rh = fct 0 e.formula_exists_pure e.formula_exists_heap in 
          let rp = f_p_simp rp in
          mkExists_w_lbl e.formula_exists_qvars rh rp 
              e.formula_exists_type e.formula_exists_flow 
              e.formula_exists_branches e.formula_exists_pos e.formula_exists_label
              (*Exists {e with formula_exists_pure = rp; formula_exists_heap = rh}*)
    | Base b ->
          let rp,rh = fct 0 b.formula_base_pure b.formula_base_heap in 
          let rp = f_p_simp rp in
          mkBase_w_lbl rh rp b.formula_base_type  b.formula_base_flow b.formula_base_branches b.formula_base_pos b.formula_base_label
              (*Base {b with formula_base_pure = rp; formula_base_heap = rh} *) in
  if not !Globals.allow_pred_spec then f
  else
    (
        Gen.Profiling.push_time "prune_preds_filter";
        let f1 = filter_formula_memo f simp_b in
        Gen.Profiling.pop_time "prune_preds_filter";
        Gen.Profiling.push_time "prune_preds";
        let nf = helper_formulas f1 in   
        Gen.Profiling.pop_time "prune_preds";
        nf
    )

and prune_preds prog (simp_b:bool) (f:formula):formula =   
  let p1 = string_of_bool in
  let p2 = Cprinter.string_of_formula in
  Debug.no_2 "prune_preds" p1 p2 p2 (fun _ _ -> prune_preds_x prog simp_b f) simp_b f

and heap_prune_preds_mix prog (hp:h_formula) (old_mem:MCP.mix_formula): (h_formula*MCP.mix_formula*bool)= match old_mem with
  | MCP.MemoF f -> 
        let r1,r2,r3 = heap_prune_preds prog hp f [] in
        (r1, MCP.MemoF r2, r3)
  | MCP.OnePF _ -> (hp,old_mem,false)

and heap_prune_preds prog (hp:h_formula) (old_mem: memo_pure) ba_crt : (h_formula * memo_pure * bool)= 
  let pr = Cprinter.string_of_h_formula in
  let pr1 = Cprinter.string_of_memo_pure_formula in
  let pr2 (h,o,r) = pr_triple Cprinter.string_of_h_formula pr1 string_of_bool (h,o,r) in
  Debug.no_2 "heap_prune_preds" pr pr1 pr2 (fun _ _ -> heap_prune_preds_x prog hp old_mem ba_crt) hp old_mem

and heap_prune_preds_x prog (hp:h_formula) (old_mem: memo_pure) ba_crt : (h_formula * memo_pure * bool)= 
  match hp with
    | Star s ->
          let ba1 =ba_crt@(heap_baga prog s.h_formula_star_h1) in
          let ba2 =ba_crt@(heap_baga prog s.h_formula_star_h2) in
          let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_star_h1 old_mem ba2 in
          let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_star_h2 mem1 ba1 in
          (mkStarH h1 h2 s.h_formula_star_pos , mem2 , (changed1 or changed2))
              (*(Star {  
                h_formula_star_h1 = h1;
                h_formula_star_h2 = h2;
                h_formula_star_pos = s.h_formula_star_pos }, mem2, (changed1 or changed2) )*)
    | Conj s ->
          let ba1 =ba_crt@(heap_baga prog s.h_formula_conj_h1) in
          let ba2 =ba_crt@(heap_baga prog s.h_formula_conj_h2) in
          let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_conj_h1 old_mem ba2 in
          let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_conj_h2 mem1 ba1 in
          (Conj {  
              h_formula_conj_h1 = h1;
              h_formula_conj_h2 = h2;
              h_formula_conj_pos = s.h_formula_conj_pos }, mem2, (changed1 or changed2) )
    |Phase  s ->
         let ba1 =ba_crt@(heap_baga prog s.h_formula_phase_rd) in
         let ba2 =ba_crt@(heap_baga prog s.h_formula_phase_rw) in
         let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_phase_rd old_mem ba2 in
         let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_phase_rw mem1 ba1 in
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
                  let not_null_form = CP.BForm ((CP.Neq (CP.Var (d.h_formula_data_node,no_pos),CP.Null no_pos,no_pos), None), None) in
                  let null_form = (CP.Eq (CP.Var (d.h_formula_data_node,no_pos), CP.Null no_pos,no_pos), None) in
                  let br_lbl = [(1,"")] in
                  let new_hp = DataNode{d with 
	                  h_formula_data_remaining_branches = Some br_lbl;
	                  h_formula_data_pruning_conditions = [ (null_form,br_lbl)];} in
                  let new_mem = MCP.memoise_add_pure_P_m old_mem not_null_form in
                  (new_hp, new_mem, true))           
    | ViewNode v ->   
          let v_def = look_up_view_def v.h_formula_view_pos prog.prog_view_decls v.h_formula_view_name in
          let fr_vars = (CP.SpecVar (Named v_def.view_data_name, self, Unprimed)):: v_def.view_vars in
          let to_vars = v.h_formula_view_node :: v.h_formula_view_arguments in
          let zip = List.combine fr_vars to_vars in
          let (rem_br, prun_cond, first_prune, chg) =  
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
                                  let and_is = MCP.fold_mem_lst_cons (CP.BConst (true,no_pos), None) [corr] false true !Globals.prune_with_slice in
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
              let aliases = MCP.memo_get_asets ba_crt new_mem2 in
              let ba_crt = ba_crt@(List.concat(List.map (fun c->CP.EMapSV.find_equiv_all c aliases ) ba_crt)) in
              let n_l = List.filter (fun c-> 
                  let c_ba,_ = List.find (fun (_,d)-> c=d) v_def.view_prune_conditions_baga in
                  let c_ba = List.map (CP.subs_one zip) c_ba in
                  not (Gen.BList.disjoint_eq CP.eq_spec_var ba_crt c_ba)) rem_br in
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
                let ni = MCP.create_memo_group_wrapper new_add_invs Implied_P in
                (*let _ = print_string ("adding: "^(Cprinter.string_of_memoised_list ni)^"\n") in*)
                let mem_o_inv = MCP.memo_change_status old_dism_invs new_mem2 in 
                ( Gen.Profiling.inc_counter "prune_cnt"; Gen.Profiling.add_to_counter "dropped_branches" (List.length l_prune);
                (new_hp, MCP.merge_mems_m mem_o_inv ni true, true) )
            else 
              if not first_prune then 
                (ViewNode{v with h_formula_view_pruning_conditions = l_no_prune;},new_mem2, false)
              else 
                let ai = (lookup_view_invs_with_subs rem_br v_def zip) in
                let gr_ai = MCP.create_memo_group_wrapper ai Implied_P in     
                let l_no_prune = List.filter (fun (_,c)-> (List.length(Gen.BList.intersect_eq (=) c rem_br))>0) l_no_prune in
                let new_hp = ViewNode {v with  h_formula_view_remaining_branches = Some rem_br;h_formula_view_pruning_conditions = l_no_prune;} in
                (new_hp, MCP.merge_mems_m new_mem2 gr_ai true, true) in
            (r_hp,r_memo,r_b)

and split_linear_node (h : h_formula) : (h_formula * h_formula) list = split_linear_node_guided [] h

(* and split_linear_node (h : h_formula) : (h_formula * h_formula) =  *)
(*         let prh = Cprinter.string_of_h_formula in *)
(*         let pr (h1,h2) = "("^(prh h1)^","^(prh h2)^")" in *)
(*         Debug.no_1 "split_linear_node" Cprinter.string_of_h_formula pr split_linear_node_x h *)

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
(* 	                        (ln1, mkStarH r1 h2 pos) *)
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
  Debug.no_2 "split_linear_node_guided" Cprinter.string_of_spec_var_list Cprinter.string_of_h_formula pr split_linear_node_guided_x vars h

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
    | Star  h-> splitter h.h_formula_star_h1 h.h_formula_star_h2 mkStarH h.h_formula_star_pos in
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
  | Star  h-> splitter h.h_formula_star_h1 h.h_formula_star_h2 mkStarH h.h_formula_star_pos in
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
	  let (pf,il) = bf in
      match pf with
        | Cpure.BVar (v,l)-> [bf]
        | Cpure.Lt (e1,e2,l)-> 
	          if (Cpure.of_interest e1 e2 interest_vars) then [(Cpure.Lt(e1,e2,l), il)]
	          else []
        | Cpure.Lte (e1,e2,l) -> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Lte(e1,e2,l), il)]
	          else []
        | Cpure.Gt (e1,e2,l) -> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Lt(e2,e1,l), il)]
	          else []
        | Cpure.Gte(e1,e2,l)-> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Lte(e2,e1,l), il)]
	          else []
        | Cpure.Eq (e1,e2,l) -> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Eq(e1,e2,l), il)]
	          else []
        | Cpure.Neq (e1,e2,l)-> 
	          if (Cpure.of_interest e1 e2 interest_vars)  then [(Cpure.Neq(e1,e2,l), il)]
	          else []
        | _ -> []
    end	
  | CP.Not (f1,_,_) -> List.map (fun c ->
	    let (pf,il) = c in 
	    match pf with
          | Cpure.BVar (v,l)-> c
          | Cpure.Lt (e1,e2,l)-> (Cpure.Lt (e2,e1,l), il)
          | Cpure.Lte (e1,e2,l) -> (Cpure.Lte (e2,e1,l), il)
          | Cpure.Eq (e1,e2,l) -> (Cpure.Neq (e1,e2,l) , il)
          | Cpure.Neq (e1,e2,l)-> (Cpure.Eq (e1,e2,l), il)
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
	  formula_exists_flow = fl;
      (* formula_exists_imm = imm; *)
	  formula_exists_label = lbl;
	  formula_exists_pos = pos}) -> begin
        let proots = find_pred_roots_heap qh in
        let f = Base ({formula_base_heap = qh;
		formula_base_pure = qp;
		formula_base_type = TypeTrue;
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
and unfold_context_unsat_now_x prog0 (prog:prog_or_branches) (ctx : list_context) (v : CP.spec_var) (pos : loc) : list_context =
  let ctx = unfold_context prog ctx v false pos in
  list_context_and_unsat_now prog0 ctx

and unfold_context_unsat_now prog0 (prog:prog_or_branches) (ctx : list_context) (v : CP.spec_var) (pos : loc) : list_context =
  let p1 = Cprinter.string_of_prog_or_branches in
  let p2 = Cprinter.string_of_spec_var in
  let pr_out = Cprinter.string_of_list_context in
  Debug.no_2 "unfold_context_unsat_now" p1 p2 pr_out (fun _ _ -> unfold_context_unsat_now_x prog0 prog ctx v pos) prog v

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
  let pr1 = Cprinter.string_of_list_failesc_context in
  let pr2 = CP.string_of_spec_var in
  Debug.no_2 "unfold_failesc_context" pr1 pr2 pr1
      (fun _ _ -> unfold_failesc_context_x prog ctx v already_unsat pos) ctx v

and unfold_failesc_context_x (prog:prog_or_branches) (ctx : list_failesc_context) (v : CP.spec_var) (already_unsat:bool)(pos : loc) : list_failesc_context =
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
  let pr2 = Cprinter.string_of_prog_or_branches in
  let prs = Cprinter.string_of_spec_var in
  Debug.no_4_num n "unfold" string_of_bool prs pr pr2 pr 
      (fun _ _ _ _ -> unfold_x prog f v already_unsat uf pos) already_unsat v f prog

and unfold_x (prog:prog_or_branches) (f : formula) (v : CP.spec_var) (already_unsat:bool) (uf:int) (pos : loc) : formula = match f with
  | Base ({ formula_base_heap = h;
	formula_base_pure = p;
	formula_base_branches = b;
	formula_base_flow = fl;
	formula_base_pos = pos}) -> 
        (*let _ = print_string ("\n memo before unfold: "^(Cprinter.string_of_memoised_list mem)^"\n")in*)
        unfold_baref prog h p fl v pos b [] already_unsat uf
  | Exists _ -> (*report_error pos ("malfunction: trying to unfold in an existentially quantified formula!!!")*)
        let rf = rename_bound_vars f in
        let qvars, baref = split_quantifiers rf in
        let h, p, fl, b, t = split_components baref in
        (*let _ = print_string ("\n memo before unfold: "^(Cprinter.string_of_memoised_list mem)^"\n")in*)
        let uf = unfold_baref prog h p fl v pos b qvars already_unsat uf in
        uf
  | Or ({formula_or_f1 = f1;
	formula_or_f2 = f2;
	formula_or_pos = pos}) ->
        let uf1 = unfold_x prog f1 v already_unsat uf pos in
        let uf2 = unfold_x prog f2 v already_unsat uf pos in
        let resform = mkOr uf1 uf2 pos in
        resform

and unfold_baref prog (h : h_formula) (p : MCP.mix_formula) (fl:flow_formula) (v : CP.spec_var) pos b qvars already_unsat (uf:int) : formula =
  let asets = Context.alias_nth 6 (MCP.ptr_equations_with_null p) in
  let aset' = Context.get_aset asets v in
  let aset = if CP.mem v aset' then aset' else v :: aset' in
  let unfolded_h = unfold_heap prog h aset v fl uf pos in
  let pure_f = mkBase HTrue p TypeTrue (mkTrueFlow ()) b pos in
  let tmp_form_norm = normalize_combine unfolded_h pure_f pos in
  let tmp_form = Cformula.set_flow_in_formula_override fl tmp_form_norm in
  let resform = if (List.length qvars) >0 then push_exists qvars tmp_form else tmp_form in
  (*let res_form = elim_unsat prog resform in*)
  if already_unsat then match (snd prog) with 
    | None -> 
          (* (Gen.Profiling.push_time "unfold_unsat";
          let r = elim_unsat_for_unfold (fst prog) resform in
          Gen.Profiling.pop_time "unfold_unsat";r) *)
          elim_unsat_for_unfold (fst prog) resform
    | _ -> resform
  else resform

and unfold_heap (prog:Cast.prog_or_branches) (f : h_formula) (aset : CP.spec_var list) (v : CP.spec_var) fl (uf:int) pos : formula = 
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = Cprinter.string_of_spec_var in
  let pr_out = Cprinter.string_of_formula in
  Debug.no_2 "unfold_heap" 
      (add_str "lhs heap:" pr1) 
      (add_str "lhs var:" pr2)
      pr_out
      (fun _ _ -> unfold_heap_x prog f aset v fl uf pos) f v

and unfold_heap_x (prog:Cast.prog_or_branches) (f : h_formula) (aset : CP.spec_var list) (v : CP.spec_var) fl (uf:int) pos : formula = 
  (*  let _ = print_string("unfold heap " ^ (Cprinter.string_of_h_formula f) ^ "\n\n") in*)
  match f with
    | ViewNode ({h_formula_view_node = p;
	  h_formula_view_imm = imm;       
	  h_formula_view_name = lhs_name;
	  h_formula_view_origins = origs;
	  h_formula_view_original = original;
	  h_formula_view_unfold_num = old_uf;
	  h_formula_view_label = v_lbl;
	  h_formula_view_remaining_branches = brs;
      h_formula_view_perm = perm;
	  h_formula_view_arguments = vs}) ->(*!!Attention: there might be several nodes pointed to by the same pointer as long as they are empty*)
          let uf = old_uf+uf in
          if CP.mem p aset then
	        match (snd prog) with
	          | None ->
                    let prog = fst prog in
	                let vdef = Cast.look_up_view_def pos prog.prog_view_decls lhs_name in
                    (*let _ = print_string "\n y\n" in*)
                    let joiner f = formula_of_disjuncts (fst (List.split f)) in
                    let forms = match brs with 
                      | None -> formula_of_unstruc_view_f vdef
                      | Some s -> joiner (List.filter (fun (_,l)-> List.mem l s) vdef.view_un_struc_formula) in
	                let renamed_view_formula = rename_bound_vars forms in
	                let renamed_view_formula = add_unfold_num renamed_view_formula uf in
		            (* propagate the immutability annotation inside the definition *)
	                let renamed_view_formula = propagate_imm_formula renamed_view_formula imm in

		            (*if any, propagate the fractional permission inside the definition *)
                    let renamed_view_formula = 
                      if (Perm.allow_perm ()) then
                        (match perm with 
                          | None -> renamed_view_formula
                          | Some f -> Cformula.propagate_perm_formula renamed_view_formula f) 
                      else renamed_view_formula
                    in

	                let fr_vars = (CP.SpecVar (Named vdef.view_data_name, self, Unprimed))
	                  :: vdef.view_vars in
	                let to_vars = v :: vs in
	                let res_form = subst_avoid_capture fr_vars to_vars renamed_view_formula in
			        (*let _ = print_string ("unfold pre subst: "^(Cprinter.string_of_formula renamed_view_formula)^"\n") in
			          let _ = print_string ("unfold post subst: "^(Cprinter.string_of_formula res_form)^"\n") in *)
	                let res_form = add_origins res_form origs in
				    (* let res_form = add_original res_form original in*)
				    let res_form = set_lhs_case res_form false in (* no LHS case analysis after unfold *)
		            (*let res_form = struc_to_formula res_form in*)
	                CF.replace_formula_label v_lbl res_form
	          | Some (base , br, (pred_id,to_vars)) -> (* base case unfold *)
                    (* ensures that only view with a specific pred and arg are base-case unfolded *)
			        let flag = if (pred_id=lhs_name) 
                    then  
                      (try 
                        (List.fold_left2 (fun a c1 c2-> a&&(CP.eq_spec_var c1 c2)) true to_vars vs)
                      with _ -> 
                          print_endline("\nWARNING : mis-matched list lengths");
                          print_endline("Pred name :"^pred_id);
                          print_endline("vars1     :"^(pr_list (Cprinter.string_of_spec_var) vs));
                          print_endline("vars2     :"^(pr_list (Cprinter.string_of_spec_var) to_vars));
                          false
                      )
                    else false 
                    in
	                if flag 
	                then  
                      (* perform base-case unfold *)
                      CF.replace_formula_label v_lbl  (CF.formula_of_mix_formula_with_branches_fl base br fl no_pos)
	                else formula_of_heap f pos
          else
	        formula_of_heap_fl f fl pos
    | Star ({h_formula_star_h1 = f1;
	  h_formula_star_h2 = f2}) ->
          let uf1 = unfold_heap_x prog f1 aset v fl uf pos in
          let uf2 = unfold_heap_x prog f2 aset v fl uf pos in
          normalize_combine_star uf1 uf2 pos
    | Conj ({h_formula_conj_h1 = f1;
	  h_formula_conj_h2 = f2}) ->
          let uf1 = unfold_heap_x prog f1 aset v fl uf pos in
          let uf2 = unfold_heap_x prog f2 aset v fl uf pos in
          normalize_combine_conj uf1 uf2 pos
    | Phase ({h_formula_phase_rd = f1;
	  h_formula_phase_rw = f2}) ->
          let uf1 = unfold_heap_x prog f1 aset v fl uf pos in
          let uf2 = unfold_heap_x prog f2 aset v fl uf pos in
          normalize_combine_phase uf1 uf2 pos
    | _ -> formula_of_heap_fl f fl pos

(*
  vvars: variables of interest
  evars: those involving this will be on the rhs
  otherwise move to the lhs
*)
and split_universal_x ((f0 : CP.formula), f0b) (evars : CP.spec_var list) 
      (expl_inst_vars : CP.spec_var list)(impl_inst_vars : CP.spec_var list)
      (vvars : CP.spec_var list) (pos : loc) 
      = let ((a,b),x,y)=split_universal_a (f0,f0b) evars expl_inst_vars impl_inst_vars vvars pos in
      ((elim_exists_pure_formula a,b),x,y)

and split_universal ((f0 : CP.formula), f0b) (evars : CP.spec_var list) 
      (expl_inst_vars : CP.spec_var list)(impl_inst_vars : CP.spec_var list)
      (vvars : CP.spec_var list) (pos : loc) 
      =
  let vv = evars (*impl_inst_vars*) in
  Debug.no_2 "split_universal" (fun (f,_)->Cprinter.string_of_pure_formula f)
      (fun _ -> (Cprinter.string_of_spec_var_list evars)^"/Impl="^(Cprinter.string_of_spec_var_list impl_inst_vars)^"/Expl="^(Cprinter.string_of_spec_var_list expl_inst_vars)^"/view vars:"^ (Cprinter.string_of_spec_var_list vvars)) (fun ((f1,_),(f2,_),_) -> (Cprinter.string_of_pure_formula f1)^"/"^ (Cprinter.string_of_pure_formula f2)) (fun f vv -> split_universal_x f evars expl_inst_vars impl_inst_vars vvars pos)
      (f0,f0b) vv
      (*
        vvars: variables of interest
        evars: those involving this will be on the rhs
        otherwise move to the lhs
      *)

(*
  and split_universal ((f0 : CP.formula), f0b) (evars : CP.spec_var list) 
  (expl_inst_vars : CP.spec_var list)(impl_inst_vars : CP.spec_var list)
  (vvars : CP.spec_var list) (pos : loc) 
  =
  let vv = evars (*impl_inst_vars*) in
  Debug.no_2 "split_universal" 
  (fun (f,_)->Cprinter.string_of_pure_formula f)
  (fun _ -> 
  ("\n ### evars = " ^ Cprinter.string_of_spec_var_list evars)
  ^"\n ### impl_inst_vars = "^(Cprinter.string_of_spec_var_list impl_inst_vars)
  ^"\n ### expl_inst_vars = "^(Cprinter.string_of_spec_var_list expl_inst_vars)
  ^"\n ### vvars = "^ (Cprinter.string_of_spec_var_list vvars)) 
  (fun ((f1,_),(f2,_),_) -> 
  ( "\n ### to_ante = " ^ Cprinter.string_of_pure_formula f1)
  ^"\n ### to_conseq = "^ (Cprinter.string_of_pure_formula f2)) 
  (fun f vv -> split_universal_x f evars expl_inst_vars impl_inst_vars vvars pos)
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
  (*TO CHECK: should include impl_inst_vars or not*)
  let instantiate = List.filter (fun v -> List.mem v (evars@expl_inst_vars(*@impl_inst_vars*))) conseq_fv in
  let instantiate_b = List.map (fun fv_list -> List.filter (fun v -> List.mem v (evars@expl_inst_vars(*@impl_inst_vars*))) fv_list) conseq_fv_b in
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

  Debug.devel_zprint (lazy ("split_universal: evars: " ^ (String.concat ", " (List.map Cprinter.string_of_spec_var evars)))) pos;
  Debug.devel_zprint (lazy ("split_universal: expl_inst_vars: "^ (String.concat ", "(List.map Cprinter.string_of_spec_var expl_inst_vars)))) pos;
  Debug.devel_zprint (lazy ("split_universal: vvars: "^ (String.concat ", "(List.map Cprinter.string_of_spec_var vvars)))) pos;
  Debug.devel_zprint (lazy ("split_universal: to_ante: "^ (Cprinter.string_of_pure_formula_branches (to_ante, to_ante_b)))) pos;
  Debug.devel_zprint (lazy ("split_universal: to_conseq: "^ (Cprinter.string_of_pure_formula_branches (to_conseq, to_conseq_b)))) pos;
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

and memo_normalize_to_CNF_n1 (f: memo_pure) pos : memo_pure = 
  List.map (fun c-> {c with memo_group_slice = List.map (fun c-> normalize_to_CNF_new c pos) c.memo_group_slice}) f

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

(*LDK: add rhs_p*)
and fold_op p c vd v (rhs_p: MCP.mix_formula) u loc =
  Gen.Profiling.no_2 "fold" (fold_op_x(*debug_2*) p c vd v rhs_p) u loc

(* and fold_op p c vd v u loc = *)
(*   Gen.Profiling.no_2 "fold" (fold_op_x(\*debug_2*\) p c vd v) u loc *)

(* and fold_debug_2 p c vd v u loc =  *)
(*   Debug.no_2 "fold_op " (fun c -> match c with *)
(*     | Ctx c -> Cprinter.string_of_formula c.es_formula *)
(*     | _ -> "CtxOR!")  *)
(*       Cprinter.string_of_h_formula  *)
(*       (fun (c,_) -> match c with | FailCtx _ -> "Fail" | _ -> "Success") *)
(*       (fun c v -> fold_op_x p c v u loc) c v *)

(* and fold_debug p c v u loc =  *)
(*   Debug.no_2 "fold_op " Cprinter.string_of_context Cprinter.string_of_h_formula (fun (c,_) -> Cprinter.string_of_list_context c) *)
(*       (fun c v -> fold_op_x p c v u loc) c v *)
(**************************************************************)
(**************************************************************)
(**************************************************************)

(*LDK: add rhs_p*)
and fold_op_x prog (ctx : context) (view : h_formula) vd (rhs_p: MCP.mix_formula) (use_case:CP.formula option) (pos : loc): (list_context * proof) =
  (* and fold_op_x prog (ctx : context) (view : h_formula) vd (* (p : CP.formula) *) (use_case:CP.formula option) (pos : loc): (list_context * proof) = *)
  let pr (x,_) = Cprinter.string_of_list_context x in
  let id x = x in
  let ans = ((* ("use-case : "^string_of_bool use_case) *)
      (* ^ *)"\n context:"^(Cprinter.string_of_context ctx)
      ^"\n rhs view :"^(Cprinter.string_of_h_formula view) 
      ^"\n rhs_p (pure) :"^(Cprinter.string_of_mix_formula rhs_p)) in
  let pr2 x = match x with
    | None -> "None"
    | Some (f) -> Cprinter.string_of_struc_formula f.view_formula in
  Debug.no_2 "fold_op" 
      pr2 id pr
      (fun _ _ -> fold_op_x1  prog (ctx : context) (view : h_formula) vd rhs_p (use_case:CP.formula option) (pos : loc)) vd ans


and fold_op_x1 prog (ctx : context) (view : h_formula) vd (rhs_p : MCP.mix_formula)
      (use_case:CP.formula option) (pos : loc): (list_context * proof) = match view with
        | ViewNode ({ h_formula_view_node = p;
          h_formula_view_name = c;
          h_formula_view_imm = imm;
          h_formula_view_label = pid;
          h_formula_view_remaining_branches = r_brs;
          h_formula_view_perm = perm; 
          h_formula_view_arguments = vs}) -> begin
            try
              let vdef = match vd with 
                | None -> look_up_view_def_raw prog.Cast.prog_view_decls c 
                | Some vd -> vd in
              (* is there a benefit for using case-construct during folding? *)
              let brs = filter_branches r_brs vdef.Cast.view_formula in
              (* let form = if use_case then brs else Cformula.case_to_disjunct brs in*)
              let form = if use_case==None then Cformula.case_to_disjunct brs else brs in 
              (*let form = Cformula.case_to_disjunct brs in *)
              let renamed_view_formula = rename_struc_bound_vars form in
	          (****)  
              let renamed_view_formula = 
	            if (isImm imm) || (isLend imm) then 
	              propagate_imm_struc_formula renamed_view_formula imm
	            else
	              renamed_view_formula
              in 
	          (***)

		      (*LDK: IMPORTANT
                if any, propagate the fractional permission inside the definition *)
              let renamed_view_formula =
                if (Perm.allow_perm ()) then
                  (match perm with
                    | None -> renamed_view_formula
                    | Some f -> Cformula.propagate_perm_struc_formula renamed_view_formula f)
                else renamed_view_formula
              in
              let fr_vars = (CP.SpecVar (Named vdef.Cast.view_data_name, self, Unprimed)) :: vdef.view_vars in
              let to_vars = p :: vs in
              let view_form = subst_struc_avoid_capture fr_vars to_vars renamed_view_formula in

              (*ENHANCE universal lemmas:
                propagate constraint on univ_vars into view_form*)
              let uni_vars = vdef.view_uni_vars in
              let new_uni_vars = CP.subst_var_list_avoid_capture fr_vars to_vars uni_vars in
              let to_fold_view = MCP.find_rel_constraints rhs_p new_uni_vars in
              let view_form = add_mix_formula_to_struc_formula to_fold_view view_form 
              in
              (*propagate*)
              let view_form = 
                if (Perm.allow_perm ()) then
                  (match perm with
                    | None -> view_form
                    | Some permvar ->
                          let to_fold_view = MCP.find_rel_constraints rhs_p [permvar] in
                          add_mix_formula_to_struc_formula to_fold_view view_form)
                else view_form
              in
              let view_form = add_struc_origins view_form (get_view_origins view) in
              let view_form = CF.replace_struc_formula_label pid view_form in
              let view_form = match use_case with 
                | None -> view_form 
                | Some f -> push_case_f f view_form in
              Debug.devel_zprint (lazy ("do_fold: LHS ctx:" ^ (Cprinter.string_of_context_short ctx))) pos;
              Debug.devel_zprint (lazy ("do_fold: RHS view: " ^ (Cprinter.string_of_h_formula view))) pos;
              Debug.devel_zprint (lazy ("do_fold: view_form: " ^ (Cprinter.string_of_struc_formula view_form))) pos;
              let estate = estate_of_context ctx pos in
              (*LDK: propagate es_vars from the estate to FOLD context
                to avoid proving es_vars as universal vars when finishing FOLDING*)
              (*Because we propagate some pure constrains into view formula 
                when FOLDING. we also have to propagate es_vars from the 
                estate into FOLDING context to avoid. Is it SOUND? Indeed, 
                we need to propagate es_vars whose constraints are propagated 
                into view formula when FOLDING.*)
  		      (*TO CHECK: does the below give new information instead of the above*)
              (*LDK: IMPORTANT
                if frac var is an existential variable, transfer it into folded view*)
              (*add fracvar into list of parameters*)
              let vs = 
                if (Perm.allow_perm ()) then
                  match perm with
                    | None -> vs
                    | Some f -> f::vs
                else vs
              in
              (* vs may contain non-existential free vars! *)
              (* let new_es = {estate with es_evars = vs (\*Gen.BList.remove_dups_eq (=) (vs @ estate.es_evars)*\)} in *)
              (* let impl_vars = Gen.BList.intersect_eq  CP.eq_spec_var vs estate.es_gen_impl_vars in  *)
              (* TODO : why must es_gen_impl_vars to be added to es_vars ??? *)
              let new_es = {estate with es_evars = (*estate.es_evars@impl_vars*)Gen.BList.remove_dups_eq (=) (vs @ estate.es_evars)} in
              (* let new_es = estate in *)
              let new_ctx = Ctx new_es in
	          (*let new_ctx = set_es_evars ctx vs in*)
              let rs0, fold_prf = heap_entail_one_context_struc_nth "fold" prog true false new_ctx view_form pos None in
              (* let rs0 = remove_impl_evars rs0 impl_vars in *)
              (* let _ = print_string ("\nbefore fold: " ^ (Cprinter.string_of_context new_ctx)) in *)
              (* let _ = print_string ("\nview: " ^ (Cprinter.string_of_h_formula view)) in *)
              (* let _ = print_string ("\nafter fold: " ^ (Cprinter.string_of_list_context rs0)) in *)
              let tmp_vars = p :: (estate.es_evars @ vs) in
	          (**************************************)
	          (*        process_one 								*)
	          (**************************************)
              let rec process_one_x (ss:CF.steps) rs1  =
	            Debug.devel_zprint (lazy ("fold: process_one: rs1:\n"^ (Cprinter.string_of_context rs1))) pos;
	            match rs1 with
	              | OCtx (c1, c2) ->
		                (*
		                  It is no longer safe to assume that rs will be conjunctive.
		                  The recursive folding entailment call (via case splitting
		                  for example) can turn ctx to a disjunctive one, hence making
		                  rs disjunctive.
		                *)
		                let tmp1 = process_one_x (CF.add_to_steps ss "left OR 3 on ante") c1 in
		                let tmp2 = process_one_x (CF.add_to_steps ss "right OR 3 on ante") c2 in
		                let tmp3 = (mkOCtx tmp1 tmp2 pos) in
		                tmp3
	              | Ctx es ->
		                (* let es = estate_of_context rs pos in *)
                        let es = CF.overwrite_estate_with_steps es ss in
		                let w = Gen.BList.difference_eq CP.eq_spec_var  es.es_evars tmp_vars in
		                let tmp_pure = elim_exists_pure w es.es_pure true pos in
                        (*LDK: remove duplicated conjuncts in the estate, 
                          which are generated because one perm var can be folded 
                          into many perm vars in many heap nodes. These generated
                          permvars might create many duplicated constraints*)
                        let mix_f, rest = tmp_pure in
                        let mix_f = CF.remove_dupl_conj_eq_mix_formula mix_f in
                        let tmp_pure = mix_f,rest in 
		                let res_rs = Ctx {es with es_evars = estate.es_evars;
				            es_pure = tmp_pure; es_prior_steps = (ss @ es.es_prior_steps);} in
		                Debug.devel_zprint (lazy ("fold: context at beginning of fold: "^ (Cprinter.string_of_spec_var p) ^ "\n"^ (Cprinter.string_of_context ctx))) pos;
		                Debug.devel_zprint (lazy ("fold: context at end of fold: "^ (Cprinter.string_of_spec_var p) ^ "\n"^ (Cprinter.string_of_context res_rs))) pos;
		                Debug.devel_zprint (lazy ("fold: es.es_pure: " ^(Cprinter.string_of_mix_formula_branches es.es_pure))) pos;
		                res_rs in
              let process_one (ss:CF.steps) fold_rs1 = 
                let pr = Cprinter.string_of_context  in
                Debug.no_1 "fold_op: process_one" pr pr (fun _ -> process_one_x (ss:CF.steps) fold_rs1) fold_rs1 in

	          let res = match rs0 with
                | FailCtx _ -> rs0
                | SuccCtx l -> SuccCtx (List.map (process_one []) l) in
	          (res, fold_prf)
            with
	          | Not_found -> report_error no_pos ("fold: view def not found:"^c^"\n") 
          end
        | _ ->
              Debug.devel_zprint (lazy ("fold: second parameter is not a view: "^ (Cprinter.string_of_h_formula view))) pos;
              report_error no_pos ("fold: second parameter is not a view\n") 
	              (*([], Failure)*)

and process_fold_result ivars prog is_folding estate (fold_rs0:list_context) p2 vs2 base2 pos : (list_context * proof list) =
  let pr1 = Cprinter.string_of_list_context_short in
  let pro x = pr1 (fst x) in
  let pr2 = pr_list Cprinter.string_of_spec_var in
  let pr3 x = Cprinter.string_of_formula (CF.Base x) in
  Debug.no_3 "process_fold_result" pr1 pr2 pr3 pro (fun _ _ _-> process_fold_result_x ivars prog is_folding estate (fold_rs0:list_context) p2 vs2 base2 pos )  
      fold_rs0 (p2::vs2) base2
and process_fold_result_x ivars prog is_folding estate (fold_rs0:list_context) p2 vs2 base2 pos : (list_context * proof list) =
  let pure2 = base2.formula_base_pure in
  let resth2 = base2.formula_base_heap in
  let type2 = base2.formula_base_type in
  let branches2 = base2.formula_base_branches in
  let flow2 = base2.formula_base_flow in
  let rec process_one_x (ss:CF.steps) fold_rs1 = match fold_rs1 with
    | OCtx (c1, c2) ->
	      let tmp1, prf1 = process_one_x (add_to_steps ss "left OR 4 in ante") c1 in
	      let tmp2, prf2 = process_one_x  (add_to_steps ss "right OR 4 in ante") c2 in
	      let tmp3 = or_list_context tmp1 tmp2 in
	      let prf3 = Prooftracer.mkOrLeft fold_rs1 (Base base2) [prf1; prf2] in 
	      (tmp3, prf3)
    | Ctx fold_es ->
          let fold_es = CF.overwrite_estate_with_steps fold_es ss in
          let e_pure = MCP.fold_mem_lst (CP.mkTrue pos) true true (fst fold_es.es_pure) in
	      let (to_ante, to_ante_br), (to_conseq, to_conseq_br), new_evars = 
            split_universal (e_pure, snd fold_es.es_pure) fold_es.es_evars fold_es.es_gen_expl_vars fold_es.es_gen_impl_vars vs2 pos in
	      let tmp_conseq = mkBase resth2 pure2 type2 flow2 branches2 pos in
	      let new_conseq = normalize 6 tmp_conseq (CF.replace_branches to_conseq_br (formula_of_pure_N to_conseq pos)) pos in
	      let new_ante = normalize 7 fold_es.es_formula (CF.replace_branches to_ante_br (formula_of_pure_N to_ante pos)) pos in
          let new_ante = filter_formula_memo new_ante false in
	      let new_consumed = fold_es.es_heap in
          let impl_vars = Gen.BList.intersect_eq CP.eq_spec_var vs2 (CP.fv to_ante) in
          let new_impl_vars = Gen.BList.difference_eq CP.eq_spec_var estate.es_gen_impl_vars impl_vars in        
	      (* let _ = print_string("new_consumed = " ^ (Cprinter.string_of_h_formula new_consumed) ^ "\n") in *)
          (* TODO : change estate to fold_es *)
	      let new_es = {(* fold_es *) estate with 
              es_heap = new_consumed;
              es_formula = new_ante;
              es_evars = new_evars;
              es_unsat_flag =false;
              es_gen_impl_vars = new_impl_vars;
              es_trace = fold_es.es_trace;
              es_orig_ante = fold_es.es_orig_ante;
              es_infer_vars = fold_es.es_infer_vars;
              es_infer_vars_rel = fold_es.es_infer_vars_rel;
              es_infer_vars_dead = fold_es.es_infer_vars_dead;
              es_infer_heap = fold_es.es_infer_heap;
              es_infer_pure = fold_es.es_infer_pure;
              es_infer_pure_thus = fold_es.es_infer_pure_thus;
              es_assumed_pure = fold_es.es_assumed_pure;
              es_infer_rel = fold_es.es_infer_rel;
      	      es_imm_last_phase = fold_es.es_imm_last_phase;
              (* es_aux_conseq = CP.mkAnd estate.es_aux_conseq to_conseq pos *)} in
	      let new_ctx = (Ctx new_es) in
        Debug.devel_zprint (lazy ("process_fold_result: old_ctx before folding: "^ (Cprinter.string_of_spec_var p2) ^ "\n"^ (Cprinter.string_of_context (Ctx fold_es)))) pos;
	      Debug.devel_zprint (lazy ("process_fold_result: new_ctx after folding: "^ (Cprinter.string_of_spec_var p2) ^ "\n"^ (Cprinter.string_of_context new_ctx))) pos;
	      Debug.devel_zprint (lazy ("process_fold_result: vs2: "^ (String.concat ", "(List.map Cprinter.string_of_spec_var vs2)))) pos;
	      Debug.devel_zprint (lazy ("process_fold_result: to_ante: "^ (Cprinter.string_of_pure_formula to_ante))) pos;
	      Debug.devel_zprint (lazy ("process_fold_result: to_conseq: "^ (Cprinter.string_of_pure_formula to_conseq))) pos;
	      Debug.devel_zprint (lazy ("process_fold_result: new_conseq:\n"^ (Cprinter.string_of_formula new_conseq))) pos;
          (* WN : we need to restore es_infer_vars here *)
          let new_ctx = Inf.restore_infer_vars_ctx ivars new_ctx in
	      let rest_rs, prf = heap_entail_one_context prog is_folding new_ctx new_conseq pos
	      in
	      Debug.devel_zprint (lazy ("process_fold_result: context at end fold: "^ (Cprinter.string_of_spec_var p2) ^ "\n"^ (Cprinter.string_of_list_context rest_rs))) pos;
          let r = add_to_aux_conseq rest_rs to_conseq pos in
	      (r, prf) in
  let process_one (ss:CF.steps) fold_rs1 = 
    let pr1 = Cprinter.string_of_context_short  in
    let pr2 (c,_) = Cprinter.string_of_list_context_short c in
    Debug.no_1 "process_one" pr1 pr2 (fun _ -> process_one_x (ss:CF.steps) fold_rs1) fold_rs1 in
    (*Debug.no_1 "process_fold_result: process_one" pr1 pr2 (fun _ -> process_one_x (ss:CF.steps) fold_rs1) fold_rs1 in*)
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
	    Debug.devel_zprint (lazy ("Some variable introduced by existential elimination where found in the residue")) no_pos end
    | OCtx (c1, c2) ->
	      let _ = redundant_existential_check svs c1 in
	      (redundant_existential_check svs c2)

and elim_exists_pure w (f, b) lump pos =
  (elim_exists_mix_formula w f pos, List.map (fun (l, f) -> (l, elim_exists_pure_branch 3 w f pos)) b)

and elim_exists_mix_formula w f pos = 
  let pr = Cprinter.string_of_mix_formula in
  Debug.no_1 "elim_exists_mix_formula" pr pr
      (fun _ -> elim_exists_mix_formula_x w f pos) f

and elim_exists_mix_formula_x w f pos = match f with
  | MCP.MemoF f -> MCP.MemoF (elim_exists_memo_pure w f pos)
  | MCP.OnePF f -> MCP.OnePF (elim_exists_pure_branch 1 w f pos)

and elim_exists_memo_pure_x (w : CP.spec_var list) (f0 : memo_pure) pos =
  let f_simp w f pos = Gen.Profiling.push_time "elim_exists";
    let f_s = elim_exists_pure_branch 2(*_debug*) w f pos in
    Gen.Profiling.pop_time "elim_exists"; f_s in
  MCP.memo_pure_push_exists_all (f_simp,true) w f0 pos

and elim_exists_memo_pure(* _debug *) w f0 pos = 
  Debug.no_2 "elim_exists_memo_pure" Cprinter.string_of_spec_var_list Cprinter.string_of_memo_pure_formula Cprinter.string_of_memo_pure_formula
      (fun w f0 -> elim_exists_memo_pure_x w f0 pos) w f0

and elim_exists_pure_formula (f0:CP.formula) =
  match f0 with
    | CP.Exists _ ->
          (*let _ = print_string "***elim exists" in*)
          let sf=TP.simplify_a 11 f0 in
          sf
    | _ -> f0

and elim_exists_pure_formula_debug (f0:CP.formula) =
  Debug.no_1_opt (fun r -> not(r==f0)) "elim_exists_pure_formula" 
      Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula
      elim_exists_pure_formula f0


(* this method will lift out free conjuncts prior to an elimination
   of existential variables w that were newly introduced;
   r denotes that free variables from f0 that overlaps with w 
*)
and elim_exists_pure_branch (i:int) (w : CP.spec_var list) (f0 : CP.formula) pos : CP.formula =
  let pf = Cprinter.string_of_pure_formula in
  Debug.no_2 ("elim_exists_pure_branch"^(string_of_int i)) Cprinter.string_of_spec_var_list pf pf 
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
    (*remove true constraints, i.e. v=v*)
    let sf = CF.remove_true_conj_pure sf in
    (*remove duplicated conjs*)
    let sf = CF.remove_dupl_conj_eq_pure sf in
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
  let h, p, fl, b, t = CF.split_components base in
  let simpl_p =	
    if !Globals.simplify_pure then 
      MCP.simpl_memo_pure_formula simpl_b_formula simpl_pure_formula p (TP.simplify_a 1)
    else p in
  let simpl_fl = fl (*flows have nothing to simplify to*)in
  let simpl_f = CF.mkExists qvar h simpl_p t simpl_fl b (CF.pos_of_formula base) in
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
  Debug.no_1 "find_unsat" (!print_formula) (fun _ -> "")
  (fun _ -> find_unsat_x prog f) f

and find_unsat_x (prog : prog_decl) (f : formula):formula list*formula list =  
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

and is_unsat_with_branches xpure_f qvars hf mix br pos sat_subno=
  Debug.no_2 "is_unsat_with_branches" 
      (fun h -> 
          "\n hf = "  ^ (Cprinter.string_of_h_formula h)
          ^"\n xpure_f hf = " ^ Cprinter.string_of_mix_formula(fst( xpure_f hf)))
      Cprinter.string_of_mix_formula
      string_of_bool
      (fun hf mix -> is_unsat_with_branches_x xpure_f qvars hf mix br pos sat_subno) hf mix

and is_unsat_with_branches_x xpure_f qvars hf mix br pos sat_subno =
  (* let wrap_exists f =  List.fold_left (fun a qv -> CP.Exists (qv, a, None, pos)) f qvars in*)
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
	  formula_base_branches = br;
	  formula_base_pos = pos}) ->
          is_unsat_with_branches (fun f-> let a,b,_,_ = xpure_heap 1 prog f 1 in (a,b)) [] h p br pos sat_subno
    | Exists ({ formula_exists_qvars = qvars;
      formula_exists_heap = qh;
      formula_exists_pure = qp;
      formula_exists_branches = br;
      formula_exists_pos = pos}) ->
          is_unsat_with_branches (fun f-> let a,b,_,_ = xpure_heap 1 prog f 1 in (a,b)) qvars qh qp br pos sat_subno

and unsat_base_nth(*_debug*) n prog (sat_subno:  int ref) f  : bool = 
  (*unsat_base_x prog sat_subno f*)
  Debug.no_1 "unsat_base_nth" 
      Cprinter.string_of_formula string_of_bool
      (fun _ -> unsat_base_x prog sat_subno f) f
      

and elim_unsat_es (prog : prog_decl) (sat_subno:  int ref) (es : entail_state) : context =
  let pr1 = Cprinter.string_of_entail_state in
  let pr2 = Cprinter.string_of_context in
  Debug.no_1 "elim_unsat_es" pr1 pr2 (fun _ -> elim_unsat_es_x prog sat_subno es) es
      
and elim_unsat_es_x (prog : prog_decl) (sat_subno:  int ref) (es : entail_state) : context =
  if (es.es_unsat_flag) then Ctx es
  else elim_unsat_es_now prog sat_subno es


and elim_unsat_ctx (prog : prog_decl) (sat_subno:  int ref) (ctx : context) : context =
  let rec helper c = match c with
    | Ctx es -> elim_unsat_es prog sat_subno es
    | OCtx(c1,c2) -> OCtx(helper c1,helper c2)
  in helper ctx

and elim_unsat_es_now (prog : prog_decl) (sat_subno:  int ref) (es : entail_state) : context =
  let pr1 = Cprinter.string_of_entail_state in
  let pr2 = Cprinter.string_of_context in
  Debug.no_1 "elim_unsat_es_now" pr1 pr2 (fun _ -> elim_unsat_es_now_x prog sat_subno es) es
  	  
and elim_unsat_es_now_x (prog : prog_decl) (sat_subno:  int ref) (es : entail_state) : context =
  let f = es.es_formula in
  let _ = reset_int2 () in
  let b = unsat_base_nth "1" prog sat_subno f in
  let es = { es with es_unsat_flag = true } in
  if not b then Ctx es else 
	false_ctx_with_orig_ante es f no_pos

and elim_unsat_ctx_now (prog : prog_decl) (sat_subno:  int ref) (ctx : context) : context =
  let rec helper c = match c with
    | Ctx es -> elim_unsat_es_now prog sat_subno es
    | OCtx(c1,c2) -> OCtx(helper c1,helper c2)
  in helper ctx

and elim_unsat_for_unfold (prog : prog_decl) (f : formula) : formula = 
  Debug.no_1 "elim_unsat_for_unfold" (Cprinter.string_of_formula) (Cprinter.string_of_formula)
	  (fun f -> elim_unsat_for_unfold_x prog f) f	
      
and elim_unsat_for_unfold_x (prog : prog_decl) (f : formula) : formula = match f with
  | Or _ -> elim_unsat_all prog f 
  | _ -> f

and elim_unsat_all prog (f : formula): formula = 
  Debug.no_1 "elim_unsat_all" (Cprinter.string_of_formula) (Cprinter.string_of_formula)
	  (fun f -> elim_unsat_all_x prog f) f	
	  
and elim_unsat_all_x prog (f : formula): formula = match f with
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
  Debug.no_2 "elim_unsat " (fun c-> "?") (Cprinter.string_of_formula) (Cprinter.string_of_formula) elim_unsat_all prog f

and get_eqns_free (st : ((CP.spec_var * CP.spec_var) * branch_label) list) (evars : CP.spec_var list) (expl_inst : CP.spec_var list) 
      (struc_expl_inst : CP.spec_var list) pos : (CP.formula * (branch_label * CP.formula) list)*(CP.formula * (branch_label * CP.formula) list)*
      (CP.spec_var * CP.spec_var) list = 
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr_p =  Cprinter.string_of_pure_formula in
  let pr_st l  = pr_list (fun (c,_)-> pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var c) l in
  let pr_st2 l  = pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) l in
  let pr ((lhs,_),(rhs,_),s) = (pr_pair pr_p pr_p (lhs,rhs))^"subst:"^(pr_st2 s) in
  Debug.no_4 "get_eqns_free" pr_st pr_svl pr_svl pr_svl pr (fun _ _ _ _ -> get_eqns_free_x (st : ((CP.spec_var * CP.spec_var) * branch_label) list) (evars : CP.spec_var list) (expl_inst : CP.spec_var list) 
      (struc_expl_inst : CP.spec_var list) pos) st evars expl_inst struc_expl_inst

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
  Debug.no_3 "subs_to_inst_vars" pr2 pr_svl pr_svl pr_r (fun _ _ _-> subs_to_inst_vars_x st ivars impl_vars pos) st ivars impl_vars

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
  Debug.no_2 "get_eqns_expl_inst" pr2 pr_svl pr_r (fun _ _ -> get_eqns_expl_inst_x st ivars pos) st ivars 

(* WN : why isn't this in cformula.ml? *)
(* removing existentail using ex x. (x=y & P(x)) <=> P(y) *)
and elim_exists (f0 : formula) : formula = match f0 with
  | Or ({ formula_or_f1 = f1;
    formula_or_f2 = f2;
    formula_or_pos = pos}) ->
        let ef1 = elim_exists f1 in
        let ef2 = elim_exists f2 in
	    mkOr ef1 ef2 pos
  | Base _ -> f0
  | Exists ({ formula_exists_qvars = qvar :: rest_qvars;
    formula_exists_heap = h;
    formula_exists_pure = p;
    formula_exists_type = t;
    formula_exists_flow = fl;
    formula_exists_branches = b;
    formula_exists_pos = pos}) ->
        let st, pp1 = MCP.get_subst_equation_memo_formula_vv p qvar in
        let r = if List.length st = 1 then
          let tmp = mkBase h pp1 t fl b pos in
          let new_baref = subst st tmp in
          let tmp2 = add_quantifiers rest_qvars new_baref in
          let tmp3 = elim_exists tmp2 in
          tmp3
        else (* if qvar is not equated to any variables, try the next one *)
          let tmp1 = mkExists rest_qvars h p t fl b pos in
          let tmp2 = elim_exists tmp1 in
          let tmp3 = add_quantifiers [qvar] tmp2 in
          tmp3 in
        r
  | Exists _ -> report_error no_pos ("Solver.elim_exists: Exists with an empty list of quantified variables")

(**************************************************************)
(* heap entailment                                            *)
(**************************************************************)

and filter_set (cl : list_context) : list_context =
  if !Globals.use_set  then cl
  else match cl with 
    | FailCtx _ -> cl
    | SuccCtx l -> if Gen.is_empty l then cl else SuccCtx [(List.hd l)]
	    (* setup the labeling in conseq and the fail context in cl *)

and heap_entail_failesc_prefix_init i (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_failesc_context)
      (conseq : 'a) pos (pid:control_path_id) ((rename_f: 'a->'a), (to_string:'a->string),
	  (f: prog_decl->bool->bool->context->'a -> loc ->control_path_id->(list_context * proof))
	  ) : (list_failesc_context * proof) =
  let pr = to_string in
  let pr2 = Cprinter.string_of_list_failesc_context in
  Debug.no_2_num i "heap_entail_failesc_prefix_init" pr2 pr (fun (c,_) -> pr2 c)
      (fun _ _ -> heap_entail_failesc_prefix_init_x prog is_folding has_post cl conseq pos pid (rename_f,to_string,f))
	  cl conseq

and heap_entail_failesc_prefix_init_x (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_failesc_context)
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
		  (* es_orig_ante   = es.es_formula; *)
		  (*es_orig_conseq = conseq ;*)}in	
      let cl_new = transform_list_failesc_context (idf,idf,(fun es-> Ctx(prepare_ctx (rename_es (reset_original_es es))))) cl in
      let entail_fct = fun c-> heap_entail_struc_list_failesc_context prog is_folding  has_post c conseq pos pid f to_string in 
      heap_entail_agressive_prunning entail_fct (prune_ctx_failesc_list prog) (fun (c,_) -> isSuccessListFailescCtx c) cl_new
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
		  (* es_orig_ante   = es.es_formula; *)
		  (*es_orig_conseq = conseq ;*)}in
      let cl_new = transform_list_partial_context ((fun es-> Ctx(prepare_ctx (rename_es es))),(fun c->c)) cl in
      heap_entail_struc_list_partial_context prog is_folding  has_post cl_new conseq pos pid f to_string
    end

and heap_entail_struc_list_partial_context (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_partial_context)
      (conseq:'a) pos (pid:control_path_id) (f: prog_decl->bool->bool->context->'a -> loc
                                              ->control_path_id->(list_context * proof)) to_string : (list_partial_context * proof) =           
  (* print_string ("\ncalling struct_list_partial_context .."^string_of_int(List.length cl)); *)
  (* print_string (Cprinter.string_of_list_partial_context cl); *)
  Debug.devel_zprint (lazy ("heap_entail_struc_list_partial_context:"^ "\nctx:\n" ^ (Cprinter.string_of_list_partial_context cl)^ "\nconseq:\n" ^ (to_string conseq))) pos; 
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
  let pr1 = Cprinter.string_of_list_failesc_context in
  let pr2 (x,_) = Cprinter.string_of_list_failesc_context x in
  Debug.no_1 "heap_entail_struc_list_failesc_context" pr1 pr2
      (fun _ -> heap_entail_struc_list_failesc_context_x prog is_folding  has_post cl 
          (conseq) pos pid f to_string) cl

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
  Debug.devel_zprint (lazy ("heap_entail_struc_partial_context:"^ "\nctx:\n" ^ (Cprinter.string_of_partial_context cl)^ "\nconseq:\n" ^ (to_string conseq))) pos; 
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
  let pr1 = Cprinter.string_of_failesc_context in
  let pr2 (x,_) = Cprinter.string_of_list_failesc_context x in
  Debug.no_1 "heap_entail_struc_failesc_context" pr1 pr2 (fun _ -> 
      heap_entail_struc_failesc_context_x prog is_folding
          (has_post)(cl) (conseq) pos (pid) f to_string) cl


and heap_entail_struc_failesc_context_x (prog : prog_decl) (is_folding : bool) 
      (has_post: bool)(cl : failesc_context) (conseq:'a) pos (pid:control_path_id) f to_string: (list_failesc_context * proof) = 
  (* print_string "\ncalling struct_partial_context .."; *)
  Debug.devel_zprint (lazy ("heap_entail_struc_failesc_context:"^ "\nctx:\n" ^ (Cprinter.string_of_failesc_context cl)^ "\nconseq:\n" ^ (to_string conseq))) pos; 
    let fail_branches, esc_branches, succ_branches  = cl in
    let res = List.map (fun (lbl,c2)-> 
		(* print_string ("\nInput ==> :"^(Cprinter.string_of_context c2)); *)
		(* print_string ("\nConseq ==> :"^(to_string conseq)); *)
		let list_context_res,prf = f (*heap_entail_one_context_struc*) prog is_folding  has_post c2 conseq pos pid in
		(* print_string ("\nOutcome ==> "^(Cprinter.string_of_list_context list_context_res)) ; *)
        (*WN :fixing incorrect handling of esc_stack by adding a skeletal structure*)
        let esc_skeletal = List.map (fun (l,_) -> (l,[])) esc_branches in
		let res = match list_context_res with
		  | FailCtx t -> [([(lbl,t)],esc_skeletal,[])]
		  | SuccCtx ls -> List.map ( fun c-> ([],esc_skeletal,[(lbl,c)])) ls in
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

(* and heap_entail_struc_init_bug (prog : prog_decl) (is_folding : bool)  (has_post: bool) ante_flow (cl : list_context) (conseq : struc_formula) pos (pid:control_path_id): (list_context * proof) = *)
(*   let conseq_flow = CF.flow_formula_of_struc_formula conseq in *)
(*   let post_check =  if CF.subsume_flow_f !Globals.error_flow_int conseq_flow then true else false in *)
(*   let conseq = (Cformula.substitute_flow_in_struc_f !norm_flow_int conseq_flow.CF.formula_flow_interval conseq ) in *)
(*   let (ans,prf) = heap_entail_struc_init prog is_folding has_post cl conseq pos pid in *)
(*   (CF.convert_must_failure_to_value ans ante_flow conseq post_check, prf) *)

and heap_entail_struc_init_bug_orig (prog : prog_decl) (is_folding : bool)  (has_post: bool) (cl : list_context) (conseq : struc_formula) pos (pid:control_path_id): (list_context * proof) =
  let (ans,prf) = heap_entail_struc_init prog is_folding has_post cl conseq pos pid in
  (CF.convert_must_failure_to_value_orig ans, prf)

and heap_entail_struc_init_bug_inv_x (prog : prog_decl) (is_folding : bool)  (has_post: bool) (cl : list_context) (conseq : struc_formula) pos (pid:control_path_id): (list_context * proof) =
  let f1 = CF.struc_formula_is_eq_flow conseq !error_flow_int in
  let f2 = CF.list_context_is_eq_flow cl !norm_flow_int in
  if f1 && f2 then
    begin
      let conseq = (CF.struc_formula_subst_flow conseq (CF.mkNormalFlow())) in
      let (ans,prf) = heap_entail_struc_init_bug_orig prog is_folding has_post cl conseq pos pid in
      (CF.invert_outcome ans,prf)
    end
  else
    heap_entail_struc_init_bug_orig prog is_folding has_post cl conseq pos pid 

and heap_entail_struc_init_bug_inv (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_context) (conseq : struc_formula) pos (pid:control_path_id): (list_context * proof) =
  Debug.no_2 "heap_entail_struc_init_bug_inv" Cprinter.string_of_list_context Cprinter.string_of_struc_formula
      (fun (ls,_) -> Cprinter.string_of_list_context ls) (fun a c -> heap_entail_struc_init_bug_inv_x prog is_folding has_post a c pos pid) cl conseq

and heap_entail_struc_init_x (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_context) (conseq : struc_formula) pos (pid:control_path_id): (list_context * proof) = 
  Debug.devel_zprint (lazy ("heap_entail_struc_init:"^ "\nctx:\n" ^ (Cprinter.string_of_list_context cl)^ "\nconseq:\n" ^ (Cprinter.string_of_struc_formula conseq))) pos; 
    match cl with
      | FailCtx fr -> (cl,Failure)
      | SuccCtx _ ->
            reset_formula_point_id();
	        let rename_es es = {es with es_formula = rename_labels_formula_ante es.es_formula}in
	        let conseq = rename_labels_struc conseq in
	        let rec prepare_ctx es = {es with 
				es_success_pts  = ([]: (formula_label * formula_label)  list)  ;(* successful pt from conseq *)
				es_residue_pts  = residue_labels_in_formula es.es_formula ;(* residue pts from antecedent *)
				es_id      = (fst (fresh_formula_label ""))              ; (* unique +ve id *)
				(* es_orig_ante   = es.es_formula; *)
				es_orig_conseq = conseq ;}in	
	        let cl_new = transform_list_context ( (fun es-> Ctx(prepare_ctx (rename_es es))),(fun c->c)) cl in
            let entail_fct = fun c-> heap_entail_struc prog is_folding  has_post c conseq pos pid in
            let (ans,prf) = heap_entail_agressive_prunning entail_fct (prune_list_ctx prog) (fun (c,_)-> not (isFailCtx c)) cl_new in
            (CF.list_context_simplify ans,prf)

and heap_entail_struc_init (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_context) (conseq : struc_formula) pos (pid:control_path_id): (list_context * proof) = 
  (*print just length of residue ctx list*)
  let length_ctx ctx = match ctx with
    | CF.FailCtx _ -> 0
    | CF.SuccCtx ctx0 -> List.length ctx0 in
  let pr_out (ctx_lst, pf) = string_of_int (length_ctx ctx_lst) in 
  Debug.no_1 "heap_entail_struc_init" (fun _ -> "?") pr_out (fun _ -> heap_entail_struc_init_x prog is_folding has_post cl conseq pos pid) prog

(* check entailment:                                          *)
(* each entailment should produce one proof, be it failure or *)
(* success. *)
and heap_entail_struc_x (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_context) (conseq : struc_formula) pos pid: (list_context * proof) =
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

and heap_entail_struc (prog : prog_decl) (is_folding : bool)  (has_post: bool)(cl : list_context) (conseq : struc_formula) pos (pid:control_path_id): (list_context * proof) =
  Debug.no_2 "heap_entail_struc" Cprinter.string_of_list_context Cprinter.string_of_struc_formula
      (fun (ls,_) -> Cprinter.string_of_list_context ls) (fun a c -> heap_entail_struc_x prog is_folding has_post a c pos pid) cl conseq

and heap_entail_one_context_struc p i1 hp cl cs pos pid =
  Gen.Profiling.do_3 "heap_entail_one_context_struc" (heap_entail_one_context_struc_x(*_debug*) p i1 hp cl) cs pos pid

and heap_entail_one_context_struc_nth n p i1 hp cl cs pos pid =
  let str="heap_entail_one_context_struc" in
  Gen.Profiling.do_3_num n str (heap_entail_one_context_struc_debug p i1 hp cl) cs pos pid

and heap_entail_one_context_struc_debug p i1 hp cl cs pos pid =
  Debug.no_1 "heap_entail_one_context_struc" 
      Cprinter.string_of_context (fun (lctx, _) -> Cprinter.string_of_list_context lctx) 
      (fun cl -> heap_entail_one_context_struc_x p i1 hp cl cs pos pid) cl

and heap_entail_one_context_struc_x (prog : prog_decl) (is_folding : bool)  has_post (ctx : context) (conseq : struc_formula) pos pid : (list_context * proof) =
  Debug.devel_zprint (lazy ("heap_entail_one_context_struc:"^ "\nctx:\n" ^ (Cprinter.string_of_context ctx)^ "\nconseq:\n" ^ (Cprinter.string_of_struc_formula conseq))) pos;
    if isAnyFalseCtx ctx then
      (*set context as bot*)
      (* let bot_ctx = CF.change_flow_into_ctx false_flow_int ctx in *)
      (* why change to false_flow_int? *)
      let bot_ctx = ctx in
      (* check this first so that false => false is true (with false residual) *)
      ((SuccCtx [bot_ctx]), UnsatAnte)
    else(* if isConstFalse conseq then
	       (--[], UnsatConseq)
	       else *)
      if isConstETrue conseq then
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
  Debug.no_2 "heap_entail_after_sat_struc" Cprinter.string_of_context
	  Cprinter.string_of_struc_formula
	  (fun (lctx, _) -> Cprinter.string_of_list_context lctx)
	  (fun _ _ -> heap_entail_after_sat_struc_x prog is_folding has_post ctx conseq pos pid ss) ctx conseq
	  
and heap_entail_after_sat_struc_x prog is_folding has_post
      ctx conseq pos pid (ss:steps) : (list_context * proof) =     
  match ctx with
    | OCtx (c1, c2) ->
          Debug.devel_zprint (lazy ("heap_entail_after_sat_struc:" ^ "\nctx:\n" ^ (Cprinter.string_of_context ctx)^ "\nconseq:\n" ^ (Cprinter.string_of_struc_formula conseq))) pos;
          let rs1, prf1 = heap_entail_after_sat_struc prog is_folding
            has_post c1 conseq pos pid (CF.add_to_steps ss "left OR 5 on ante") in
          let rs2, prf2 = heap_entail_after_sat_struc prog is_folding
            (* WN : what is init_caller for? *)
            has_post c2 conseq pos pid (CF.add_to_steps ss "right OR 5 on ante") in
	      ((or_list_context rs1 rs2),(mkOrStrucLeft ctx conseq [prf1;prf2]))
    | Ctx es -> begin
        Debug.devel_zprint (lazy ("heap_entail_after_sat_struc: invoking heap_entail_conjunct_lhs_struc"^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx)^ "\nconseq:\n" ^ (Cprinter.string_of_struc_formula conseq))) pos;
        (*let es = {es with es_formula = prune_preds prog es.es_formula } in*)
        let es = (CF.add_to_estate_with_steps es ss) in
        let tmp, prf = heap_entail_conjunct_lhs_struc prog is_folding has_post (Ctx es) conseq pos pid in
	    (filter_set tmp, prf)
      end

and sem_imply_add prog is_folding  ctx (p:CP.formula) only_syn:(context*bool) = 
  let pr1 = Cprinter.string_of_context_short in
  let pr2 = Cprinter.string_of_pure_formula in
  let pr3 = pr_pair pr1 string_of_bool in
  Debug.no_2 "sem_imply_add" pr1 pr2 pr3 
      (fun _ _ -> sem_imply_add_x prog is_folding  ctx (p:CP.formula) only_syn) ctx p


and sem_imply_add_x prog is_folding  ctx (p:CP.formula) only_syn:(context*bool) = match ctx with
  | OCtx _ -> report_error no_pos ("sem_imply_add: OCtx encountered \n")
  | Ctx c -> 
        if (CP.isConstTrue p) then (ctx,true)
        else
	      if (sintactic_search c.es_formula p) then 
            (* let _ = print_endline "syn true!" in *)
            (ctx,true)
	      else if only_syn then (print_string "only syn\n"; (ctx,false))
	      else
	        let b = (xpure_imply prog is_folding  c p !Globals.imply_timeout_limit) in
	        if b then 
              (* let _ = print_endline "xpure true!" in *)
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
  Debug.no_2 "heap_entail_conjunct_lhs_struc"
      pr (Cprinter.string_of_struc_formula)
      (fun (a,b) -> Cprinter.string_of_list_context a)
      (fun ctx conseq -> heap_entail_conjunct_lhs_struc_x p is_folding  has_post ctx conseq pos pid) ctx conseq

and heap_entail_conjunct_lhs_struc_x
      (prog : prog_decl) 
      (is_folding : bool) 
      
      (has_post:bool)
      (ctx_00 : context) 
      (conseq : struc_formula) pos pid : (list_context * proof) =

  (* let estate = match ctx_00 with
     | OCtx _ -> report_error no_pos ("heap_entail_conjunct_lhs_struc : OCtx encountered \n")
     | Ctx es -> es in*)


  (* and inner_entailer ctx conseq = *)
  (*   Debug.no_2 "inner_entailer" (Cprinter.string_of_context) (Cprinter.string_of_struc_formula) (fun (l,p) -> (Cprinter.string_of_list_context l)^"\nProof:"^(Prooftracer.string_of_proof p)) inner_entailer_a ctx conseq *)

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

  let rec helper_inner (ctx11: context) (f: ext_formula) : list_context * proof =
	Debug.no_2 "helper_inner"
	    Cprinter.string_of_context
	    Cprinter.string_of_ext_formula
	    (fun (lc, _) -> Cprinter.string_of_list_context lc)
	    helper_inner_x ctx11 f

  and helper_inner_x (ctx11 : context) (f:ext_formula) : list_context * proof = 
    begin
      match f with
        | ECase b   ->
              let ctx = add_to_context_num 1 ctx11 "case rule" in
              let ivs = collect_infer_vars ctx11 in
              let case_brs = b.formula_case_branches in
              let case_vs = match case_brs with
                | [] -> []
                | (p,_)::_ -> CP.fv p in
              let d = CP.diff_svl case_vs ivs in
              if (d==[] && case_vs!=[]) then
                begin
                  (* place to add case LHS to infer_pure *)
	              (* let _ = print_endline ("WN ECase IVars:"^(Cprinter.string_of_spec_var_list ivs)) in *)
	              (* let _ = print_endline ("WN ECase CVars:"^(Cprinter.string_of_spec_var_list case_vs)) in *)
                  (*
                    for each (c1,c2) from case_brs
                    (i) add c1 into ctx11 & also infer_pure & perform unsat
                    filter away those that are false
                    perform entail against each c2
                    combine result as union
                  *)
                  let rs = List.map (fun (c1,c2) ->	
                    (combine_context_and_unsat_now prog (ctx) (MCP.memoise_add_pure_N (MCP.mkMTrue pos) c1), c1, c2)) case_brs in
                  (* remove away false context : need to keep at least one? *)
                  let rs2 = List.filter (fun (c1,_,_) -> not(isAnyFalseCtx c1)) rs in
                  let rs = if rs2==[] then [List.hd rs] else rs2 in
                  let res = List.map (fun (ctx,p,rhs) ->
                      let ctx = prune_ctx prog ctx in
                      let (r,prf) = inner_entailer 9 ctx rhs in
                      (* add infer_pure to result ctx in *)
                      let r = add_infer_pure_to_list_context [p] r in
                      (r,prf)) rs in
	              let rez1, rez2 = List.split res in
                  let rez1 = List.fold_left (fun a c -> list_context_union a c) (List.hd rez1) (List.tl rez1) in
	              (rez1, (mkCaseStep ctx [f] rez2))
                end
              else
	            (*let _ = print_string ("\nstart case:"^(Cprinter.string_of_ext_formula f)^"\n") in*)
                (* print_endline ("XXX helper of inner entailer"^Cprinter.string_of_prior_steps (CF.get_prior_steps ctx)); *)
	            if (List.length b.formula_case_exists)>0 then 
	              let ws = CP.fresh_spec_vars b.formula_case_exists in
	              let st = List.combine b.formula_case_exists ws in
	              let new_struc = subst_struc st [(ECase {b with formula_case_exists = []})]in
	              let new_ctx = push_exists_context ws ctx in
	              let nc,np = inner_entailer 1 new_ctx new_struc in 
	              (nc, (mkEexStep ctx [f] np))
	            else if case_brs==[] (* (List.length b.formula_case_branches )=0 *) then ((SuccCtx [ctx]),TrueConseq)
	            else 
	              let rec helper l = match l with
	                | [] -> None
	                | (p,e)::t -> 
		                  let tt = (syn_imply ctx p) in
		                  (*print_string ("\n -------------:\n"^(Cprinter.string_of_context ctx)^"\n\n"^
		                    (Cprinter.string_of_pure_formula p)^"\n\n"^(string_of_bool tt)^"\n") ;*)
		                  if tt then Some (p,e) else helper t in
			      (* Find the branch whose condition is satisfied by the current context *)
			      (* Because these conditions are disjoint, the context can only satisfy at most one condition *)
	              let r = helper case_brs (* b.formula_case_branches *) in
	              let r = match r with
	                | None -> begin
                      (*let _ = print_endline ("###: 4.1") in*)
		                List.map (fun (c1, c2) -> 
			                let n_ctx = combine_context_and_unsat_now prog (ctx) (MCP.memoise_add_pure_N (MCP.mkMTrue pos) c1) in 
                            (*this unsat check is essential for completeness of result*)
                          (*should return Failure bot instead*)
				          if (isAnyFalseCtx n_ctx) then
                           (* let _ = print_endline ("###: 4.1.1") in*)
                            let es = CF.estate_of_context n_ctx no_pos in
                            let err_msg = "31. proving precondtition: unreachable" in
                            let fe = mk_failure_bot err_msg Globals.undefined_error in
                            (CF.mkFailCtx_in (Basic_Reason ({fc_message =err_msg;
                                            fc_current_lhs  = es;
		                                    fc_prior_steps = es.es_prior_steps;
		                                    fc_orig_conseq = [f] ;
		                                    fc_current_conseq = CF.formula_of_heap HFalse pos;
		                                    fc_failure_pts =  [];}, fe)), UnsatAnte)
                           (* (SuccCtx[n_ctx], UnsatAnte)*)
				            else
					          let n_ctx = prune_ctx prog n_ctx in
					          inner_entailer 2 n_ctx c2) case_brs (* b.formula_case_branches *) 
				            end
	                | Some (p, e) -> begin
				            [inner_entailer 3 ctx e] end in
	              let rez1, rez2 = List.split r in
                  let rez1 = List.fold_left (fun a c -> or_list_context (*list_context_union*) a c) (List.hd rez1) (List.tl rez1) in
	              (rez1, (mkCaseStep ctx [f] rez2))
        | EBase ({
		      formula_ext_explicit_inst = expl_inst;
		      formula_ext_implicit_inst = impl_inst;
		      formula_ext_exists = base_exists;
		      formula_ext_base = formula_base;
		      formula_ext_continuation = formula_cont;
              (*formula_ext_complete = pre_c;*)
		      formula_ext_pos = struc_pos;
		  } as b) -> 
              if (List.length base_exists) > 0 then 
	            let ws = CP.fresh_spec_vars base_exists in
	            let st = List.combine base_exists ws in
	            let new_struc = subst_struc st [(EBase {b with formula_ext_exists = []})]in
	            let new_ctx = push_exists_context ws ctx11 in
	            let nc, np = inner_entailer 4 new_ctx new_struc in 
	            (nc, (mkEexStep ctx11 [f] np))
	          else 
			    (*let _ = print_string ("An Hoa :: inner_entailer_a :: check point 1\n") in*)
	            let n_ctx = (push_expl_impl_context expl_inst impl_inst ctx11 ) in
	            let n_ctx_list, prf = heap_entail_one_context prog (if (List.length formula_cont)>0 then true else is_folding) n_ctx formula_base pos in
			    (*let n_ctx_list = List.filter  (fun c -> not (isFalseCtx c)) n_ctx_list in*)
	            let n_ctx_list = pop_expl_impl_context expl_inst impl_inst n_ctx_list in
			    (match n_ctx_list with
	              | FailCtx _ ->(* let _ = print_endline ("###: 1") in *) (n_ctx_list, prf)
	              | SuccCtx _ ->
		                if (List.length formula_cont)>0 then
                          (*let _ = print_endline ("###: 2") in*)
                          let res, n_rpf = heap_entail_struc prog is_folding has_post n_ctx_list formula_cont pos pid in
                          (* let res, n_rpf = List.split (List.map (fun c->inner_entailer 5 c formula_cont) sc) in *)
                          (* let res = fold_context_left res in *)
                          let res = if !wrap_exists_implicit_explicit
					      then push_exists_list_context (expl_inst@impl_inst) res 
					      else res in
                          (res, n_rpf) (* (mkBaseStep ctx11 [f] prf (mkCaseStep ctx11 [f] n_rpf)) *)
		                else
                        (*  let _ = print_endline ("###: 3") in*)
                          let res = if !wrap_exists_implicit_explicit
					      then push_exists_list_context (expl_inst@impl_inst) n_ctx_list 
		                  else n_ctx_list in
		                  (*let _ = print_string ("\nresidue: "^(Cprinter.string_of_context_list res)^"\n  "^(string_of_bool (isFalseCtx (List.hd res)))^"\n") in*)
				          (res,prf)
                )
        | EAssume (ref_vars, post, (i,y)) ->
		      if not has_post then report_error pos ("malfunction: this formula "^ y ^" can not have a post condition!")
	          else
                (*check reachable or not*)
                (*let ctx1,_= heap_entail_one_context prog is_folding ctx11 (mkTrue_nf pos) pos in*)
	            let rs = clear_entailment_history (fun x -> Some (xpure_heap_symbolic prog x 0)) ctx11 in
	            (*let _ =print_string ("before post:"^(Cprinter.string_of_context rs)^"\n") in*)
                (*let _ =print_string ("before post:"^(Cprinter.string_of_formula post)^"\n") in *)
                (* TOCHECK : why compose_context fail to set unsat_flag? *)
	            let rs1 = CF.compose_context_formula rs post ref_vars Flow_replace pos in
	            (*let _ = print_string ("\n after post:"^(Cprinter.string_of_context rs1)^"\n") in*)
	            let rs2 = CF.transform_context (elim_unsat_es_now prog (ref 1)) rs1 in
                (*let _ = print_string ("\n after post and unsat:"^(Cprinter.string_of_context rs2)^"\n") in*)
	            let rs3 = add_path_id rs2 (pid,i) in
                let rs4 = prune_ctx prog rs3 in
                 (******************************************************)
                (*foo5,foo6 in hip/err3.ss*)
                let helper ctx postcond=
                   let es = CF.estate_of_context ctx pos in
                    let lp1 = CF.list_pos_of_formula es.CF.es_formula in
                    let lp2 = CF.list_pos_of_formula postcond in
                    let ll = CF.get_lines (lp1 @ lp2) in
                   (* let _ = print_endline ("\nxxx:" ^ (Cprinter.string_of_list_int ll)) in*)
                    (es, ll)
                in
                let invert_ctx ctx postcond=
                  (* let _ = print_endline ("###: " ^ (Cprinter.string_of_context ctx)) in*)
                 (* if CF.isAnyFalseListCtx ctx1 then SuccCtx [ctx] (*should return bot: unreachable*)
                  else*)
                   (*  let _ = print_endline ("###: 3") in*)
                  (*let f1 = CF.struc_formula_is_eq_flow conseq !error_flow_int in *)
                  let fl = CF.flow_formula_of_formula postcond in
                  if CF.equal_flow_interval fl.CF.formula_flow_interval !top_flow_int then
                    let es, ll = helper ctx postcond in
                    let err_name = (exlist # get_closest fl.CF.formula_flow_interval) in
                    (* let err_msg = "32. proving precondtition: error scenarios (" ^ err_name ^ *)
                    (*  ")\n    locs: [" ^ (Cprinter.string_of_list_int ll) ^ "]" in *)
                    let err_msg = "may_err (" ^ err_name ^
                     ") LOCS: [" ^ (Cprinter.string_of_list_int ll) ^ "]"in
                    let fe = mk_failure_may err_msg Globals.fnc_error in
                    FailCtx (Basic_Reason ({fc_message =err_msg;
                                            fc_current_lhs  = es;
		                                    fc_prior_steps = es.es_prior_steps;
		                                    fc_orig_conseq = [f] ;
		                                    fc_current_conseq = post;
		                                    fc_failure_pts =  [];}, fe))
                  else if CF.subsume_flow_f !error_flow_int fl then
                     let es, ll = helper ctx postcond in
                     let err_name = (exlist # get_closest fl.CF.formula_flow_interval) in
                    (* let err_msg = "32. proving precondtition: error scenarios (" ^ err_name ^ *)
                    (*  ")\n    LOCS: [" ^ (Cprinter.string_of_list_int ll) ^ "]"in *)
                     let err_msg = "must_err (" ^ err_name ^
                     ") LOCS: [" ^ (Cprinter.string_of_list_int ll) ^ "]"in
                    let fe = mk_failure_must err_msg Globals.fnc_error in
                    FailCtx (Basic_Reason ({fc_message =err_msg;
                                            fc_current_lhs  = es;
		                                    fc_prior_steps = es.es_prior_steps;
                                            fc_orig_conseq  = [f];
		                                    fc_current_conseq = post;
		                                    fc_failure_pts =  [];}, fe))
                  else (SuccCtx [ctx])
                in
                (******************************************************)
                if not !Globals.disable_failure_explaining then
                 (* let _ = print_endline ("********\n" ^ (Cprinter.string_of_context rs4)) in*)
	            (invert_ctx rs4 post ,TrueConseq)
                else (SuccCtx [rs4] ,TrueConseq)
        | EInfer e -> 
              (* ignores any EInfer on the RHS *) 
              (* assumes each EInfer contains exactly one continuation *)
              (* TODO : change the syntax of EInfer? *)
              let c=e.Cformula.formula_inf_continuation in
              helper_inner_x ctx11 c
	    (*| EVariance e ->
          (*let entail_f = fun ctx m pos -> 
            fst (heap_entail_one_context prog false ctx m pos) in
          let _ = Term.check_term_measure entail_f ctx11 e pos in*)
          helper_inner_x ctx11 e.CF.formula_var_continuation*)
    end 
 
  and inner_entailer i (ctx22 : context) (conseq : struc_formula): list_context * proof =
	Debug.no_2_num i "inner_entailer"
	    Cprinter.string_of_context
	    Cprinter.string_of_struc_formula
	    (fun (cl, _) -> Cprinter.string_of_list_context cl)
	    (fun _ _ -> inner_entailer_x i ctx22 conseq) ctx22 conseq
	    
  and inner_entailer_x i (ctx22 : context) (conseq : struc_formula): list_context * proof = 
    let _ = match ctx22 with 
	  | OCtx _ ->
            Error.report_warning {
				Error.error_loc = post_pos#get;
				Error.error_text = ("[inner entailer" ^ (string_of_int i) ^ "] unexpected dealing with OCtx " ^ (string_of_int (count_octx ctx22)) ^ "\n" ^ (Cprinter.string_of_context_short ctx22))
            }
	  | _ -> () in
	if (List.length conseq) > 0 then	
	  (* this call captures an OCtx, why?? *)
	  let ctx = CF.add_to_context_num 2 ctx22 "para OR on conseq" in
	  let r = List.map (helper_inner ctx) conseq in
	  let l1,l2 = List.split r in
	 ((fold_context_left l1), (mkCaseStep ctx conseq l2))
	else 
	  (* TODO : can do a stronger falsity check on LHS *)
	  (CF.mkFailCtx_in(Trivial_Reason (CF.mk_failure_must "struc conseq is [] meaning false" Globals.sl_error)) , UnsatConseq)
		  (* ((SuccCtx [ctx]),TrueConseq) *)
  in
  inner_entailer 8 ctx_00 conseq 
	  (*let adv_u = advance_unfold_struc prog ctx_00 conseq in
	    if adv_u==[] then
		inner_entailer 8 ctx_00 conseq 
	    else
	  (* inner_entailer 8 ctx_00 conseq	*)
		let a = snd (List.hd adv_u) in
		print_string "sta1\n";
	    process_unfold prog estate conseq a is_folding pos has_post pid*)

and heap_entail_init (prog : prog_decl) (is_folding : bool)  (cl : list_context) (conseq : formula) pos : (list_context * proof) =
  Debug.no_2 "heap_entail_init"
	  Cprinter.string_of_list_context
	  Cprinter.string_of_formula
	  (fun (rs, _) -> Cprinter.string_of_list_context rs)
	  (fun cl conseq -> heap_entail_init_x prog is_folding cl conseq pos) cl conseq
	  
	  
and heap_entail_init_x (prog : prog_decl) (is_folding : bool)  (cl : list_context) (conseq : formula) pos : (list_context * proof) =
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
			  (* es_orig_ante   = es.es_formula; *)
			  es_orig_conseq = struc_formula_of_formula conseq pos;} in	
	      let cl_new = transform_list_context ((fun es-> Ctx(prepare_es(rename_es (reset_original_es es)))),(fun c->c)) cl in
	      let conseq_new = conseq in
	      heap_entail prog is_folding  cl_new conseq_new pos

and heap_entail_debug
      p is_folding  cl conseq 
      pos : (list_context * proof) = 
  Debug.no_2 "heap_entail---------\n\n"
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
  Debug.no_2 "heap_entail_one_context" (Cprinter.string_of_context) (Cprinter.string_of_formula) (fun (l,p) -> Cprinter.string_of_list_context l) 
      (fun ctx conseq -> heap_entail_one_context_a prog is_folding  ctx conseq pos) ctx conseq

(*   and heap_entail_one_context prog is_folding  ctx conseq pos =  *)
(* heap_entail_one_context_a prog is_folding  ctx conseq pos *)

and heap_entail_one_context_a (prog : prog_decl) (is_folding : bool)  (ctx : context) (conseq : formula) pos : (list_context * proof) =
  Debug.devel_zprint (lazy ("heap_entail_one_context:"^ "\nctx:\n" ^ (Cprinter.string_of_context ctx)^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq)^"\n")) pos;
    if isAnyFalseCtx ctx then
      (* check this first so that false => false is true (with false residual) *)
      (SuccCtx [ctx], UnsatAnte)
    else if isStrictConstTrue conseq then
      (SuccCtx [ctx], TrueConseq)
          (* else if isAnyFalseCtx ctx then *)
          (*   (SuccCtx [ctx], UnsatAnte) *)
    else
      (* UNSAT check *)
      let ctx = elim_unsat_ctx prog (ref 1) ctx in
      let ctx = set_unsat_flag ctx true in 
      if isAnyFalseCtx ctx then
        (SuccCtx [ctx], UnsatAnte)
      else
        heap_entail_after_sat prog is_folding ctx conseq pos ([])

and heap_entail_after_sat prog is_folding  (ctx:CF.context) (conseq:CF.formula) pos
      (ss:CF.steps) : (list_context * proof) =
  Debug.no_2 "heap_entail_after_sat"
	  (Cprinter.string_of_context)
	  (Cprinter.string_of_formula)
	  (fun (l,p) -> Cprinter.string_of_list_context l)
      (fun ctx conseq -> heap_entail_after_sat_x prog is_folding ctx conseq pos ss) ctx conseq

and heap_entail_after_sat_x prog is_folding  (ctx:CF.context) (conseq:CF.formula) pos
      (ss:CF.steps) : (list_context * proof) =
  match ctx with
    | OCtx (c1, c2) ->
          Debug.devel_zprint (lazy ("heap_entail_after_sat:"^ "\nctx:\n" ^ (Cprinter.string_of_context ctx)^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq))) pos;
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
        Debug.devel_zprint (lazy ("heap_entail_after_sat: invoking heap_entail_conjunct_lhs"^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx)^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq))) pos;
		(*print_string ("An Hoa CHECKPOINT 2664 :: heap_entail_after_sat\n");
		  print_string ("heap_entail_after_sat: invoking heap_entail_conjunct_lhs" ^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx) ^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq));*) 
        (* print_string ("going: "^(Cprinter.string_of_formula es.es_formula)^"\n") ;*)
        (* let es = {es with es_formula = prune_preds prog true es.es_formula} in *)
        (* let conseq = prune_preds prog true conseq in *)
        let es = (CF.add_to_estate_with_steps es ss) in
        let tmp, prf = heap_entail_conjunct_lhs prog is_folding  (Ctx es) conseq pos in  
		(*print_string ("heap_entail_after_sat: output context:\n" ^ (Cprinter.string_of_list_context tmp) ^ "\n");*)  
	    (filter_set tmp, prf)
      end

and heap_entail_conjunct_lhs prog is_folding  (ctx:context) conseq pos : (list_context * proof) = 
  let pr1 = (fun _ -> "prog_decl") in
  let pr2 = string_of_bool in
  let pr3 = Cprinter.string_of_context in
  let pr4 = Cprinter.string_of_formula in
  let pr5 = string_of_loc in
  let pr_res (ctx,_) = ("\n ctx = "^(Cprinter.string_of_list_context ctx)) in
  (* let pr_res (ctx,proof) = ("\n ctx = "^(Cprinter.string_of_list_context ctx) *)
  (* ^ "\n proof = " ^ (string_of_proof proof) *)
  (* ^"\n\n") in *)
  Debug.no_5 "heap_entail_conjunct_lhs" pr1 pr2 pr3 pr4 pr5 pr_res heap_entail_conjunct_lhs_x prog is_folding ctx conseq pos

(* and heap_entail_conjunct_lhs p  = heap_entail_conjunct_lhs_x p *)

(* check entailment when lhs is normal-form, rhs is a conjunct *)
and heap_entail_conjunct_lhs_x prog is_folding  (ctx:context) (conseq:CF.formula) pos : (list_context * proof) =
  (* pre ; LHS is not an OCtx *)
  (* is LHS really conjunctive? *)
  (* (if not(CF.is_one_context ctx) then report_error no_pos "heap_entail_one_context does not have Ctx es"); *)
  (* let lhs_flow = CF.get_flow_context ctx in *)
  (* let rhs_flow = CF.get_flow_formula conseq in *)
  (* if CF.flow_subsume lhs_flow rhs_flow then return must_error *)
  (* else  *)
  (* HOA TODO  : to unfold pred with duplicated roots on the LHS *)

  (*let _ = print_endline "AN HOA : CALL TO [heap_entail_conjunct_lhs_x] WITH INPUTS" in
	let _ = print_endline ("CONTEXT = " ^ PR.string_of_context ctx) in
	let _ = print_endline ("CONSEQ = " ^ PR.string_of_formula conseq) in*)

  (** [Internal] Collect the data and view nodes in a h_formula. 
	  @return The list of all DataNode and ViewNode **)
  let rec collect_data_view (f : h_formula) = match f with
	| Star { h_formula_star_h1 = h1; h_formula_star_h2 = h2}
	| Conj { h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
	| Phase { h_formula_phase_rd = h1; h_formula_phase_rw = h2;} ->
		  List.append (collect_data_view h1) (collect_data_view h2) 
	| DataNode _ | ViewNode _ -> [f]
	| Hole _ | HTrue | HFalse -> []
  in (* End of function collect_data_view *)

  (** [Internal] Generate the action based on the list of node and its tail **)
  let rec generate_action_x nodes eset =
    match nodes with
	| [] 
	| [_] -> Context.M_Nothing_to_do "No duplicated nodes!" 
	| x::t ->
		  (*
		    let y = List.hd t in
		  (*if ((compare_sv (get_node_var x) (get_node_var y) eset = 0)*)
		    if ((CP.eq_spec_var_aset eset (get_node_var x) (get_node_var y))
			&& (is_view x || is_view y)) then
			let mr = { Context.match_res_lhs_node = if (is_view x) then x else y;
			Context.match_res_lhs_rest = x;
			Context.match_res_holes = [] ;
			Context.match_res_type = Context.Root;
			Context.match_res_rhs_node = x;
			Context.match_res_rhs_rest = x} in
		  (* let _ = print_endline "AN HOA : START THE UNFOLDING PROCESS" in *)
			Context.M_unfold (mr,1)
		    else generate_action t eset
		  *)
		  try
			let y = List.find (fun e -> 
        (CP.eq_spec_var_aset eset (get_node_var x) (get_node_var e)) && (is_view x || is_view e)) t in
      
			(*let _ = print_string ("\ngenerate_action: x: " ^ (Cprinter.string_of_h_formula x) ^ "\n") in
			let _ = print_string ("\ngenerate_action: y: " ^ (Cprinter.string_of_h_formula y) ^ "\n") in*)
			
			let mr = { Context.match_res_lhs_node = if (is_view x) then x else y;
			Context.match_res_lhs_rest = x;
			Context.match_res_holes = [] ;
			Context.match_res_type = Context.Root;
			Context.match_res_rhs_node = x;
			Context.match_res_rhs_rest = x;
            (* Context.match_res_add_constr = CP.mkTrue no_pos; *)
            } in
			Context.M_unfold (mr,1)
		  with
      | Not_found -> generate_action t eset
		          
			      
  and generate_action nodes eset = 
    let pr = pr_list Cprinter.string_of_h_formula in
	  let pr_1 = P.EMapSV.string_of in
    let pr_2 = Context.string_of_action_res_simpl in
    Debug.no_2 "generate_action" pr pr_1 pr_2 (fun _ _ -> generate_action_x nodes eset) nodes eset

  (** [Internal] Compare two spec var syntactically. **)
  and compare_sv_syntax xn yn = match (xn,yn) with
	| (CP.SpecVar (_,_,Primed), CP.SpecVar (_,_,Unprimed)) -> -1
	| (CP.SpecVar (_,_,Unprimed), CP.SpecVar (_,_,Primed)) -> -1
	| (CP.SpecVar (_,xnn,_), CP.SpecVar (_,ynn,_)) -> 
		  if (String.compare xnn ynn)==0 then 0
          else -1
	        
  (** [Internal] Compare spec var with equality taken into account **)
  and compare_sv_x xn yn eset =
	(* let _ = print_string ("Comparing " ^ (Cprinter.string_of_spec_var xn) ^ " and " ^ (Cprinter.string_of_spec_var yn)) in *)
	
	try
	  let _,xne = List.find (fun x -> CP.eq_spec_var xn (fst x)) eset in
	  let _ = List.find (fun x -> CP.eq_spec_var yn x) xne in 
	  (* let _ = print_string " --> equal" in *)
	  0
	with
	  | Not_found -> (* let _ = print_string "\n" in *) compare_sv_syntax xn yn
	        
  (*
	if CP.eq_spec_var_aset eset xn yn then 0
	else compare_sv_syntax xn yn
  *)
  (*compare_sv_syntax xn yn*)

  and compare_sv_old xn yn eset =
	if CP.eq_spec_var_aset eset xn yn then 0
	else -1 

  (* comparing with previous method compare_sv_old *)
  and compare_sv xn yn eset =
    let pr = Cprinter.string_of_spec_var in
    Debug.no_2_cmp (fun _ _ -> compare_sv_old xn yn eset) 
        "compare_sv" pr pr string_of_int (fun _ _ -> compare_sv_x xn yn eset) xn yn

  (* and compare_sv xn yn eset = *)
  (*   let pr = Cprinter.string_of_spec_var in *)
  (*   let compare_sv_old xn yn eset = *)
  (*     if CP.eq_spec_var_aset eset xn yn then 0 *)
  (*     else -1 in *)
  (*   let sameres = (compare_sv_old xn yn eset)==(compare_sv_x xn yn eset) in *)
  (*   let compare_sv_old xn yn eset = *)
  (*     Debug.no_2 "compare_sv_old" pr pr string_of_int (fun _ _ -> compare_sv_old xn yn eset) xn yn in *)
  (*    if sameres then compare_sv_x xn yn eset  *)
  (*   else   *)
  (*     let _ = compare_sv_old xn yn eset in *)
  (*     Debug.no_2 "compare_sv" pr pr string_of_int (fun _ _ -> compare_sv_x xn yn eset) xn yn *)
  in

  (** [Internal] Process duplicated pointers in an entail state **)
  let process_entail_state (es : entail_state) =
	(* Extract the heap formula *)
	let f = es.es_formula in
	(* let _ = print_endline ("heap_entail_conjunct_lhs_x :: process_entail_state :: " ^ PR.string_of_formula f) in *)
	let h,p = match f with
	  | Base b -> (b.formula_base_heap,b.formula_base_pure)
	  | Or _ -> failwith "[heap_entail_conjunct_lhs_x]::Unexpected OR formula in context!"
	  | Exists b -> (b.formula_exists_heap,b.formula_exists_pure)
	in
	let eqns = ptr_equations_with_null p in
	(* let _ = List.map (fun (x,y) -> print_string ("[" ^ (Cprinter.string_of_spec_var x) ^ "," ^ (Cprinter.string_of_spec_var y) ^ "]")) eqns in *)
	let eset = CP.EMapSV.build_eset eqns in
	(* let _ = List.map (fun (x,y) -> print_string ("[" ^ (Cprinter.string_of_spec_var x) ^ " == " ^ (String.concat "," (List.map Cprinter.string_of_spec_var y)) ^ "]\n")) eset in
	   let _ = print_string "\n" in *)
	(* Collect and sort the data and view predicates *)
	let dv = collect_data_view h in
	let dv = List.sort
	  (fun x y -> compare_sv (get_node_var x) (get_node_var y) eset)
	  dv in
	(* let _ = List.map (fun x -> print_endline (PR.string_of_h_formula x)) dv in *)
	(* Produce an action to perform *)
	let action = generate_action dv eset in
	(* Process the action to get the new entail state *)
	let b = { formula_base_heap = HTrue;
    formula_base_pure = Mcpure.mkMTrue no_pos;
    formula_base_type = TypeTrue; 
    formula_base_flow = mkTrueFlow ();
    formula_base_branches = []; 
    formula_base_label = None;
    formula_base_pos = no_pos } in
	let res = process_action 0 prog es conseq b b action [] is_folding pos in
	(* let _ = print_endline "AN HOA : THE CONTEXT BEFORE UNFOLDING" in 
	   let _ = print_endline (PR.string_of_entail_state es) in
	   let _ = print_endline "AN HOA : NEW CONTEXT AFTER UNFOLDING OF DUPLICATED ROOTS" in
     let lctx, _ = res in
	   let _ = print_endline (PR.string_of_list_context lctx) in *)
	(res, match action with
	  | Context.M_Nothing_to_do _ -> false
	  | _ -> let _ = num_unfold_on_dup := !num_unfold_on_dup + 1 in 
		(* let _ = print_endline ("[heap_entail_conjunct_lhs_x] " ^ (string_of_int !num_unfold_on_dup) ^ " unfold performed!") in *)
		true)
  in (* End of process_entail_state *)

  (* Termination: Strip the LexVar in the pure part of LHS - Move it to es_var_measures *)
  let ctx = Term.strip_lexvar_lhs ctx in

  (* Call the internal function to do the unfolding and do the checking *)
  let temp,dup = if !unfold_duplicated_pointers then
	match ctx with 
	  | Ctx es -> process_entail_state es 
	  | OCtx _ -> failwith "[heap_entail_conjunct_lhs_x]::Unexpected OCtx as input!"
  else (* Dummy result & set dup = false to do the usual checking. *)
	((FailCtx (Trivial_Reason (CF.mk_failure_must "Dummy list_context" Globals.sl_error)), Prooftracer.TrueConseq) ,false)
  in
  if dup then (* Contains duplicate --> already handled by process_action in process_entail_state *) 
	temp 
  else match conseq with
    | Or ({formula_or_f1 = f1;
	  formula_or_f2 = f2;
	  formula_or_pos = pos1}) ->
          Debug.devel_zprint (lazy ("heap_entail_conjunct_lhs: \nante:\n"
		  ^ (Cprinter.string_of_context ctx)
		  ^ "\nconseq:\n"
		  ^ (Cprinter.string_of_formula conseq))) pos;
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
	      if !Globals.allow_imm then
            begin
              Debug.devel_zprint (lazy ("heap_entail_conjunct_lhs: invoking heap_entail_split_rhs_phases")) pos;
	          heap_entail_split_rhs_phases prog is_folding  ctx conseq false pos     
            end
	      else
	        heap_entail_conjunct prog is_folding  ctx conseq [] pos     
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

(* and move_lemma_expl_inst_ctx_list (ctx:list_context)(f:mix_formula):list_context = *)
(*         let pr1 = Cprinter.string_of_list_context in *)
(*         let pr2 = Cprinter.string_of_mix_formula in *)
(*   Debug.no_2 "move_lemma_expl_inst_ctx_list" pr1 pr2 pr1  *)
(*       move_lemma_expl_inst_ctx_list_x ctx f *)


(*LDK: 25/08/2011, also instatiate ivars*)
(* and move_expl_inst_ctx_list (ctx:list_context)(f:MCP.mix_formula):list_context = *)
(*   let pr1 = Cprinter.string_of_list_context in *)
(*   let pr2 = Cprinter.string_of_mix_formula in *)
(*   Debug.no_2 "move_expl_inst_ctx_list" pr1 pr2 pr1  *)
(*       move_expl_inst_ctx_list_x ctx f *)

(* (\*TO CHECK: *\) *)
(* and move_expl_inst_ctx_list_x (ctx:list_context)(f:MCP.mix_formula):list_context =  *)
(*   let fct es =  *)
(* 	let l_inst = es.es_gen_expl_vars@es.es_gen_impl_vars@es.es_ivars in *)
(*     let f = MCP.find_rel_constraints f l_inst in *)
(*     let nf =  *)
(*       let f2 = if (es.es_evars = []) then f else  *)
(* 		(\*let wrapp_l = Gen.BList.difference_eq CP.eq_spec_var es.es_evars l_inst in*\) *)
(* 		(elim_exists_mix_formula(\*_debug*\) es.es_evars f no_pos) in *)
(* 	  (\* let _ = print_string ("moving: "^(Cprinter.string_of_mix_formula f2)^"\n") in *\) *)
(*       CF.mkStar es.es_formula (formula_of_mix_formula f2 no_pos) Flow_combine no_pos in *)
(*     (\*let f1 = formula_of_memo_pure (MCP.memo_pure_push_exists (es.es_gen_impl_vars@es.es_evars) f ) no_pos in*\) *)
(*     Ctx {es with *)
(*         (\* why isn't es_gen_expl_vars updated? *\) *)
(* 	    es_gen_impl_vars = Gen.BList.intersect_eq CP.eq_spec_var es.es_gen_impl_vars es.es_evars; *)
(* 	    es_ante_evars = es.es_ante_evars @ es.es_evars; *)
(* 	    es_formula = nf; *)
(* 	    es_unsat_flag = false; } in *)
(*   transform_list_context (fct,(fun c->c)) ctx *)

and move_expl_inst_ctx_list (ctx:list_context)(f:MCP.mix_formula):list_context =
  let pr1 = Cprinter.string_of_list_context_short in
  let pr2 = Cprinter.string_of_mix_formula in
  Debug.no_2 "move_expl_inst_ctx_list" pr1 pr2 pr1 
      move_expl_inst_ctx_list_x ctx f

(*TO CHECK: *)
and move_expl_inst_ctx_list_x (ctx:list_context)(f:MCP.mix_formula):list_context = 
  match ctx with
    | FailCtx _ -> ctx
    | SuccCtx cl ->
          let cl1 = 
            List.map (fun c ->
	            (transform_context
	                (fun es -> Ctx(move_expl_inst_estate es f)
	                ) c)) cl 
          in SuccCtx(cl1)

(*   Ctx {es with *)
(*       (\* why isn't es_gen_expl_vars updated? *\) *)
(* 	    es_gen_impl_vars = Gen.BList.intersect_eq CP.eq_spec_var es.es_gen_impl_vars es.es_evars; *)
(* 	    es_ante_evars = es.es_ante_evars @ es.es_evars; *)
(* 	    es_formula = nf; *)
(* 	    es_unsat_flag = false; } in *)
(* transform_list_context (move_expl_inst_estate,(fun c->c)) ctx *)

and get_expl_inst es (f : MCP.mix_formula) = 
  let l_inst = es.es_gen_expl_vars(*@es.es_gen_impl_vars@es.es_ivars*) in
  let f = MCP.find_rel_constraints f l_inst in
  let to_elim_vars = es.es_gen_impl_vars@es.es_evars in
  if (to_elim_vars = []) then f 
  else (elim_exists_mix_formula to_elim_vars f no_pos) 

and move_expl_inst_estate es (f : MCP.mix_formula) = 
  let nf = 
    let f2 = get_expl_inst es f in
    (* if (to_elim_vars = []) then f else  *)
	(* (elim_exists_mix_formula to_elim_vars f no_pos) in *)
    (* let _ = print_endline("cris: expl inst = " ^ (Cprinter.string_of_mix_formula f2)) in *)
    CF.mkStar es.es_formula (formula_of_mix_formula f2 no_pos) Flow_combine no_pos in
  {es with
      (* why isn't es_gen_expl_vars updated? *)
      (* es_gen_impl_vars = Gen.BList.intersect_eq CP.eq_spec_var es.es_gen_impl_vars es.es_evars; *)
      es_ante_evars = es.es_ante_evars @ es.es_gen_impl_vars@es.es_evars (*es.es_evars*);
      es_formula = nf;
      es_unsat_flag = false; } 

and move_impl_inst_estate es (f:MCP.mix_formula) = 
  let l_inst = es.es_gen_impl_vars@es.es_ivars in
  let f = MCP.find_rel_constraints f l_inst in
  let to_elim_vars = es.es_gen_expl_vars@es.es_evars in  
  let nf = 
    let f2 = if ( to_elim_vars = []) then f else 
	  (elim_exists_mix_formula to_elim_vars f no_pos) in
    (* let _ = print_endline("cris: impl inst = " ^ (Cprinter.string_of_mix_formula f2)) in *)
    (* let _ = print_endline("cris: f = " ^ (Cprinter.string_of_mix_formula f)) in *)
    CF.mkStar es.es_formula (formula_of_mix_formula f2 no_pos) Flow_combine no_pos in
  {es with
      (* why isn't es_gen_expl_vars updated? *)
      es_gen_impl_vars = Gen.BList.intersect_eq CP.eq_spec_var es.es_gen_impl_vars to_elim_vars (*es.es_evars*);
      es_ante_evars = es.es_ante_evars @ to_elim_vars;
      es_formula = nf;
      es_unsat_flag = false; } 
      



(* from a list containing equaltions of the form vi = wi -> obtain two lists [vi]  and [wi] *)
and obtain_subst l =
  match l with
    | CP.BForm ((CP.Eq(CP.Var(e1, _), CP.Var(e2, _), _), _), _)::r -> ((e1::(fst (obtain_subst r))), (e2::(snd (obtain_subst r))))
    | _::r -> ((fst (obtain_subst r)), (snd (obtain_subst r)))
    | [] -> ([],[])

and coer_target prog (coer : coercion_decl) (node:CF.h_formula) (target_rhs : CF.formula) (lhs : CF.formula) : bool =
  Debug.no_3 "coer_target" (* Cprinter.string_of_coercion  *)
      Cprinter.string_of_h_formula Cprinter.string_of_formula Cprinter.string_of_formula string_of_bool 
      (fun _ _ _ -> coer_target_a prog coer node target_rhs lhs) node lhs target_rhs

(* check whether the target of a coercion is in the RHS of the entailment *)
(* coer: the coercion lemma to be applied *)
(* node: the node to which the coercion applies *)
(* lhs and rhs - the antecedent and consequent, respectively *)
and coer_target_a prog (coer : coercion_decl) (node:CF.h_formula) (target_rhs : CF.formula) (lhs : CF.formula) : bool =
  let coer_lhs = coer.coercion_head in
  let coer_rhs = coer.coercion_body in
  let coer_lhs_heap, coer_lhs_guard,coer_lhs_flow, coer_lhs_branches, _ = split_components coer_lhs in
  let rhs_heap, rhs_pure, rhs_flow, rhs_branches, _ = split_components target_rhs in
  let lhs_heap, lhs_pure, lhs_flow, lhs_branches, _ = split_components lhs in
  (*let _ = print_string("coer_lhs_heap = " ^ (Cprinter.string_of_h_formula coer_lhs_heap) ^ "\n") in
    let _ = print_string("node = " ^ (Cprinter.string_of_h_formula node) ^ "\n") in*)
  (* node - the node to which we want to apply the coercion rule *)
  (* need to find the substitution *)
  match node, coer_lhs_heap with
    | ViewNode ({ h_formula_view_node = p1;
	  h_formula_view_name = c1;
	  h_formula_view_origins = origs;
	  h_formula_view_perm = perm1;
	  h_formula_view_arguments = ps1}),
	  ViewNode ({h_formula_view_node = p2;
	  h_formula_view_name = c2;
	  h_formula_view_perm = perm2;
	  h_formula_view_arguments = ps2}) (* when c1=c2 -> *)

    | DataNode ({ h_formula_data_node = p1;
	  h_formula_data_name = c1;
	  h_formula_data_origins = origs;
	  h_formula_data_perm = perm1;
	  h_formula_data_arguments = ps1}),
	  DataNode ({h_formula_data_node = p2;
	  h_formula_data_name = c2;
	  h_formula_data_perm = perm2;
	  h_formula_data_arguments = ps2}) when c1=c2 ->
	      begin
	        (* apply the substitution *) (*LDK: do we need to check for perm ???*)
	        let coer_rhs_new = subst_avoid_capture (p2 :: ps2) (p1 :: ps1) coer_rhs in
	        let coer_lhs_new = subst_avoid_capture (p2 :: ps2) (p1 :: ps1) coer_lhs in
	        (*let _ = print_string("coer_rhs = " ^ (Cprinter.string_of_formula coer_rhs) ^ "\n") in*)
	        (*let _ = print_string("coer_rhs_new = " ^ (Cprinter.string_of_formula coer_rhs_new) ^ "\n") in *)
	        (* find the targets from the RHS of the coercion *)
	        let top_level_vars = (CF.f_top_level_vars coer_rhs_new) in
	        let target = (List.filter (fun x -> List.mem x top_level_vars) (CF.fv coer_rhs_new)) in
	        let target = (List.filter (fun x -> (List.mem x (CF.fv coer_lhs_new))) target) in
	        (*let _ = print_string ("Target:" ^ (Cprinter.string_of_spec_var_list target) ^ "\n") in*)
	        let coer_rhs_h, _,_, _, _ = split_components coer_rhs_new in
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
  Debug.no_3 "check_one_target" pr1 pr2 pr3 string_of_bool
      (fun _ _ _ -> check_one_target_x prog node (target : CP.spec_var) (lhs_pure : MCP.mix_formula) (target_rhs_p : MCP.mix_formula) (target_rhs_h : CF.h_formula) (coer_rhs_h : CF.h_formula)) target target_rhs_p target_rhs_h 

(* check whether target appears in rhs *)
(* we need lhs_pure to compute the alias set of target *)
and check_one_target_x prog node (target : CP.spec_var) (lhs_pure : MCP.mix_formula) (target_rhs_p : MCP.mix_formula) (target_rhs_h : CF.h_formula) (coer_rhs_h : CF.h_formula)
      : bool =
  (*let _ = print_string("check_one_target: target: " ^ (Cprinter.string_of_spec_var target) ^ "\n") in*)
  let lhs_eqns = MCP.ptr_equations_with_null lhs_pure in
  let rhs_eqns = MCP.ptr_equations_with_null target_rhs_p in
  let lhs_asets = Context.alias_nth 7 (lhs_eqns@rhs_eqns) in
  let lhs_targetasets1 = Context.get_aset lhs_asets target in
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
  let lhs_asets = Context.alias_nth 8 lhs_eqns in
  let lhs_targetasets1 = Context.get_aset lhs_asets target in
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
		                let _ = Debug.devel_zprint (lazy ("Target: " ^ (Cprinter.string_of_h_formula target_node) ^ "\n")) no_pos in
		                let _ = Debug.devel_zprint (lazy ("Target match: " ^ (Cprinter.string_of_h_formula anode) ^ "\n")) no_pos in
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
  let coer_lhs_heap, _,_, _, _ = split_components coer_lhs in
  let coer_rhs_heap, _,_, _, _ = split_components coer_rhs in
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

and heap_entail_split_rhs_phases
      p is_folding  ctx0 conseq d
      pos : (list_context * proof) =
  Debug.no_2 "heap_entail_split_rhs_phases"
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
  let ctx_with_rhs =  
	let (h, p, fl, b, t) = CF.split_components conseq in
	let eqns = (MCP.ptr_equations_without_null p) in
    CF.set_context (fun es -> 
        {es with 
            es_rhs_eqset=(es.es_rhs_eqset@eqns);
            (* es_imm_pure_stk=p::es.es_imm_pure_stk; *)}) ctx_0 in
  let helper ctx_00 h p (* mix pure *) (func : CF.h_formula -> MCP.mix_formula -> CF.formula) = 

    let h1, h2, h3 = split_phase h in
    (* let _ = print_string("\nheap_entail_split_lhs: splitting h into:\n h1 (rhs) = " ^ (Cprinter.string_of_h_formula h1) ^ "\n h2 (rhs) = " ^ (Cprinter.string_of_h_formula h2) ^ "\n h3 (rhs) = " ^ (Cprinter.string_of_h_formula h3)) in *)
    if(is_true h1) && (is_true h2) && (is_true h3) then
      (* no heap on the RHS *)
      heap_entail_conjunct prog is_folding ctx_00 conseq [] pos
    else
      (* only h2!=true *)
      if ((is_true h1) && (is_true h3)) then
	    heap_n_pure_entail prog is_folding  ctx_00 conseq h2 p func true pos
      else
	    (* only h1!=true *)
	    if ((is_true h2) && (is_true h3)) then
	      heap_n_pure_entail prog is_folding  ctx_00 conseq h1 p func false pos
	    else
	      (* only h3!=true *)
	      if ((is_true h1) && (is_true h2)) then
	        let new_conseq = func h3 p in
	        if not(Cformula.contains_phase h3) then
	          (* h3 does not contain any nested phases *)
	          heap_n_pure_entail prog is_folding  ctx_00  conseq (choose_not_true_heap h1 h2 h3) p func (consume_heap new_conseq) (*drop_read_phase*) pos
 	        else
	          (* h3 contains nested phases *)
	          heap_entail_split_rhs_phases_x prog is_folding  
                  ctx_00 
                  new_conseq (consume_heap new_conseq) pos
	      else
	        let res_ctx, res_prf = 
          (	    
    		    (* this is not the last phase of the entailment *)
	              let ctx_00 = disable_imm_last_phase_ctx ctx_00 in
	              (* entail the read phase heap *)
	              let (after_rd_ctx, after_rd_prf) = heap_entail_rhs_read_phase prog is_folding  ctx_00 h1 h2 h3 func pos in
	              (* entail the write phase heap *)
	              let after_wr_ctx, after_wr_prfs = heap_entail_rhs_write_phase prog is_folding  after_rd_ctx after_rd_prf conseq h1 h2 h3 func pos in
	              (* entail the nested phase heap *)
	              heap_entail_rhs_nested_phase prog is_folding  after_wr_ctx after_wr_prfs conseq h1 h2 h3 func drop_read_phase pos
	          )
	        in 
	        (* entail the pure part *)
		(* this is the last phase of the entailment *)
		let res_ctx = enable_imm_last_phase res_ctx in
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
		                    | OCtx _ -> report_error no_pos ("Disjunctive context\n"))
		                in 
		                let new_conseq = CF.mkStar new_conseq aux_conseq_from_fold Flow_combine pos in
                        (* let _ = print_endline ("**********************************") in
                        let _ = print_endline ("heap_split_rhs new_conseq :"^(Cprinter.string_of_formula new_conseq)) in
                        let _ = print_endline ("**********************************") in *)
		                heap_entail_conjunct prog is_folding  c new_conseq []  pos) cl 
	                in
	                let res_ctx, res_prf = List.split res in
	                let res_prf = mkContextList cl (Cformula.struc_formula_of_formula conseq pos) res_prf in
	                let res_ctx = fold_context_left res_ctx in 
	                (res_ctx, res_prf)
	          | FailCtx _ -> (res_ctx, res_prf)	    
  in

  Debug.devel_zprint (lazy ("heap_entail_split_rhs_phases: 
                            \nante:\n"
  ^ (Cprinter.string_of_context ctx_0)
  ^ "\nconseq:\n"
  ^ (Cprinter.string_of_formula conseq))) pos;

  match ctx_0 with
    | Ctx estate -> begin
        let ante = estate.es_formula in
        match ante with
	      | Exists ({formula_exists_qvars = qvars;
		    formula_exists_heap = qh;
		    formula_exists_pure = qp;
		    formula_exists_type = qt;
		    formula_exists_flow = qfl;
		    formula_exists_branches = qb;
		    formula_exists_pos = pos}) ->
	            (* ws are the newly generated fresh vars for the existentially quantified vars in the LHS *)
	            let ws = CP.fresh_spec_vars qvars in
	            (* new ctx is the new context after substituting the fresh vars for the exist quantified vars *)
	            let new_ctx = eliminate_exist_from_LHS qvars qh qp qt qfl qb pos estate in
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
	                  let (h, p, fl, b, t) = CF.split_components conseq in
	                  helper ctx_with_rhs (* ctx_0 *) h p (fun xh xp -> CF.mkBase xh xp t fl b pos)
	            | Exists ({formula_exists_qvars = qvars;
		          formula_exists_heap = qh;
		          formula_exists_pure = qp;
		          formula_exists_type = qt;
		          formula_exists_flow = qfl;
		          formula_exists_branches = qb;
		          formula_exists_pos = pos}) ->
	                  (* quantifiers on the RHS. Keep them for later processing *)
	                  let ws = CP.fresh_spec_vars qvars in
	                  let st = List.combine qvars ws in
	                  let baref = mkBase qh qp qt qfl qb pos in
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


and eliminate_exist_from_LHS qvars qh qp qt qfl qb pos estate =  
  (* eliminating existential quantifiers from the LHS *)
  (* ws are the newly generated fresh vars for the existentially quantified vars in the LHS *)
  let ws = CP.fresh_spec_vars qvars in
  let st = List.combine qvars ws in
  let baref = mkBase qh qp qt qfl qb pos in
  let new_baref = subst st baref in
  (* new ctx is the new context after substituting the fresh vars for the exist quantified vars *)
  let new_ctx = Ctx {estate with
      es_formula = new_baref;
      es_ante_evars = ws @ estate.es_ante_evars;
      es_unsat_flag = false;} 
  in new_ctx

and heap_n_pure_entail(*_debug*) prog is_folding  ctx0 conseq h p func drop_read_phase pos : (list_context * proof) =
  Debug.no_3 "heap_n_pure_entail" (Cprinter.string_of_context) Cprinter.string_of_h_formula Cprinter.string_of_mix_formula
      (fun (lc,_) -> match lc with FailCtx _ -> "Not OK" | SuccCtx _ -> "OK")  (fun ctx0 h p -> heap_n_pure_entail_x prog is_folding  ctx0 conseq h p func drop_read_phase pos) ctx0 h p

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
  (* let _ = print_string("entailing the heap h = " ^ (Cprinter.string_of_h_formula h) ^ "\n") in *)
  (* let _  = print_string("*************************************************\n") in *)
  let ctx0 = disable_imm_last_phase_ctx ctx0 in
  let entail_h_ctx, entail_h_prf = heap_entail_split_lhs_phases prog is_folding  ctx0 (func h (MCP.mkMTrue pos)) (consume_heap_h_formula h) pos in
  let entail_h_ctx = enable_imm_last_phase entail_h_ctx in
  match entail_h_ctx with
    | FailCtx _ -> (entail_h_ctx, entail_h_prf)
    | SuccCtx(cl) ->
	      (* let _  = print_string("*************************************************\n") in *)
	      (* let _ = print_string("entailing the pure p = " ^ (Cprinter.string_of_mix_formula p) ^ "\n") in *)
	      (* let _  = print_string("*************************************************\n") in *)
          let entail_p = List.map 
	        (fun c -> one_ctx_entail prog is_folding  c conseq func p pos) cl  
          in
          let entail_p_ctx, entail_p_prf = List.split entail_p in
          let entail_p_prf = mkContextList cl (Cformula.struc_formula_of_formula conseq pos) entail_p_prf in
          let entail_p_ctx = fold_context_left entail_p_ctx in 
          (entail_p_ctx, entail_p_prf)

and one_ctx_entail prog is_folding  c conseq func p pos : (list_context * proof) =
  Debug.no_3 "one_ctx_entail" (Cprinter.string_of_context_short) Cprinter.string_of_formula Cprinter.string_of_mix_formula
      (* (fun (lc,_) -> match lc with FailCtx _ -> "Not OK" | SuccCtx _ -> "OK")  *)
      (fun (lc,_) -> Cprinter.string_of_list_context_short lc)
      (fun ctx0 conseq p ->  one_ctx_entail_x prog is_folding ctx0 conseq func p pos) c conseq p

and one_ctx_entail_x prog is_folding  c conseq func p pos : (list_context * proof) = 
  (match c with 
    | Ctx(estate) -> 
          (* TODO : es_aux_conseq is an input here *)
          let new_conseq = subst_avoid_capture (fst estate.es_subst) (snd estate.es_subst) (func HTrue p) in
          let aux_c = estate.es_aux_conseq in
          (* let _ = print_endline ("*********************************") in *)
          (* let _ = print_endline ("input aux_conseq:"^(Cprinter.string_of_pure_formula aux_c)) in *)
          (* let _ = print_endline ("*********************************") in *)
          let aux_conseq_from_fold = subst_avoid_capture (fst estate.es_subst) (snd estate.es_subst) (func HTrue (MCP.mix_of_pure aux_c)) in
          let new_conseq = CF.mkStar new_conseq aux_conseq_from_fold Flow_combine pos in
		  (*  let _ = print_string("context = " ^ (Cprinter.string_of_context c) ^ "\n") in		  
		      let _ = print_string("new_conseq = " ^ (Cprinter.string_of_formula new_conseq) ^ "\n") in*)
          heap_entail_conjunct prog is_folding  c new_conseq []  pos
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
    heap_entail_split_lhs_phases prog is_folding  ctx0 new_conseq false (* (consume_heap new_conseq) *) pos 
  in (after_rd_ctx, after_rd_prf)

and heap_entail_rhs_write_phase prog is_folding  after_rd_ctx after_rd_prf conseq h1 h2 h3 func pos = 
  match after_rd_ctx with
    | FailCtx _ -> (after_rd_ctx, after_rd_prf)
    | SuccCtx (cl) -> 
          (* entail the write phase *)
          (* let _ = print_string("************************************************************************\n") in *)
          (* let _ = print_string("split_rhs: entail wr phase h2 = " ^ (Cprinter.string_of_h_formula h2) ^ "\n") in *)
          (* let _ = print_string("************************************************************************\n") in *)
          (* let drop_read_phase =  *)
	      (*       if (consume_heap_h_formula h2) or (consume_heap_h_formula h3) *)
	      (*       then true *)
	      (*       else false *)
          (* in *)
          let new_conseq =
	        if (is_true h3) then
	          (func h2 (MCP.mkMTrue pos)) 
	        else
	          (func h2 (MCP.mkMTrue pos))
          in
          let after_wr_ctx, after_wr_prfs =
	        if not(is_true h2) then
	          let after_wr = List.map (fun c -> heap_entail_split_lhs_phases prog is_folding  c new_conseq true pos) cl in
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
  Debug.no_2 "insert_ho_frame_in2_formula"
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
	  formula_base_branches = b;
	  formula_base_label = l;
	  formula_base_pos = pos}) ->
	      mkBase (ho_frame h) p  t fl  b  pos
    | Exists({formula_exists_qvars = qvars;
	  formula_exists_heap = h;
	  formula_exists_pure = p;
	  formula_exists_type = t;
	  formula_exists_flow = fl;
	  formula_exists_branches = b;
	  formula_exists_label = l;
	  formula_exists_pos = pos}) ->
	      mkExists qvars (ho_frame h) p t fl b pos
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
	      let (h, p, fl, b, t) = CF.split_components f in
	      (CF.mkBase new_h p t fl b pos, h)
    | Exists({formula_exists_qvars = qvars;
	  formula_exists_heap = h;
	  formula_exists_pure = p;
	  formula_exists_type = t;
	  formula_exists_flow = fl;
	  formula_exists_branches = b;
	  formula_exists_label = l;
	  formula_exists_pos = pos }) -> 
	      (CF.mkExists qvars new_h p t fl b pos, h)
    | _ -> report_error no_pos ("solver.ml: No LHS disj should reach this point\n  ")


and heap_entail_split_lhs_phases(*_debug*)
      p is_folding  ctx0 conseq d
      pos : (list_context * proof) =
  Debug.no_2 "heap_entail_split_lhs_phases"
      (Cprinter.string_of_context)
      (fun _ -> "RHS")
      (* (Cprinter.string_of_formula) *)
      (fun (c,_) -> Cprinter.string_of_list_context c)
      (fun ctx0 conseq -> heap_entail_split_lhs_phases_x p is_folding  ctx0 conseq d pos) ctx0 conseq

(* entailment method for splitting the antecedent *)
and heap_entail_split_lhs_phases_x
      (prog : prog_decl) 
      (is_folding : bool) 
      
      (ctx0 : context) 
      (conseq : formula) 
      (drop_read_phase : bool)
      pos : (list_context * proof) =

  Debug.devel_zprint (lazy ("heap_entail_split_lhs_phases: 
                            \nante:\n"
  ^ (Cprinter.string_of_context ctx0)
  ^ "\nconseq:\n"
  ^ (Cprinter.string_of_formula conseq))) pos;

    (***** main helper method ******)
    (* called for both formula base and formula exists *)
    let rec helper_lhs h func : (list_context * proof) = 
      (* split h such that:
         h1 = rd phase
         h2 = write phase
         h3 = nested phase 
      *)
      let h1, h2, h3 = split_phase(*_debug_lhs*) h in
      (* let _ = print_string("\nheap_entail_split_lhs: splitting h into:\n h1 (lhs) = " ^ (Cprinter.string_of_h_formula h1) ^ "\n h2 (lhs) = " ^ (Cprinter.string_of_h_formula h2) ^ "\n h3 (lhs) = " ^ (Cprinter.string_of_h_formula h3)) in *)
      (* let _ = print_string("\nheap_entail_split_lhs: conseq = " ^ (Cprinter.string_of_formula conseq)) in *)
      (* let _ = print_string("\nheap_entail_split_lhs: drop_read_phase = " ^ (string_of_bool drop_read_phase)) in *)
      if ((is_true h1) && (is_true h3))
        or ((is_true h2) && (is_true h3))
      then
        (* lhs contains only one phase (no need to split) *)
        let new_ctx = CF.set_context_formula ctx0 (func (choose_not_true_heap h1 h2 h3)) in
	    (* in this case we directly call heap_entail_conjunct *)
        let final_ctx, final_prf = heap_entail_conjunct prog is_folding  new_ctx conseq []  pos in
	    match final_ctx with
	      | SuccCtx(cl) ->
	            (* substitute the holes due to the temporary removal of matched immutable nodes *) 
	            (* let _ = print_string("Substitute the imm holes \n") in *)
	            let cl1 = List.map subs_crt_holes_ctx cl in
		        (SuccCtx(cl1), final_prf)
	      | FailCtx _ -> (final_ctx, final_prf)
      else
        if ((is_true h1) && (is_true h2)) then
	      (* only the nested phase is different from true;*)
	      let new_ctx = CF.set_context_formula ctx0 (func h3) in
	      let final_ctx, final_prf = 
	        (* we must check whether this phase contains other nested phases *)
	        if not(Cformula.contains_phase h3) then
	          (* no other nested phases within h3 *)
	          (* direct call to heap_entail_conjunct *)
	          heap_entail_conjunct prog is_folding  new_ctx conseq [] pos
	        else
	          (* we need to recursively split the phases nested in h3 *)
	          (* let _ = print_string("\n\nRecursive call to heap_entail_split_lhs_phases\n") in *)
	          heap_entail_split_lhs_phases prog is_folding  new_ctx conseq drop_read_phase pos
	      in
	      match final_ctx with
	        | SuccCtx(cl) ->
		          (* substitute the holes due to the temporary removal of matched immutable nodes *) 
		          (* let _ = print_string("Substitute the holes\n") in *)
		          let cl1 = List.map subs_crt_holes_ctx cl in
		          (SuccCtx(cl1), final_prf)
	        | FailCtx _ -> (final_ctx, final_prf)

        else
	      (* lhs contains multiple phases *)
	      (******************************************************)
	      (****** the first entailment uses h1 as lhs heap ******)
	      (******************************************************)
	      let lhs_rd = func h1 in
	      let rd_ctx = CF.set_context_formula ctx0 lhs_rd in
	      Debug.devel_zprint (lazy ("heap_entail_split_lhs_phases: \ncall heap_entail_conjunct with lhs = reading phase\n")) pos;
	      (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)
	      (* let _ = print_string("split_lhs: entail using h1 = " ^ (Cprinter.string_of_h_formula h1) ^ "\n") in *)
	      (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)


	      let (with_rd_ctx, with_rd_prf) = heap_entail_conjunct prog is_folding  rd_ctx conseq [] pos in
	      let with_rd_ctx = 
	        (match with_rd_ctx with
              | FailCtx _ -> with_rd_ctx
	          | SuccCtx (cl) -> 
		            (* substitute the holes due to the temporary removal of matched immutable nodes *) 
		            (* let _ = print_string("Substitute the holes \n") in *)
		            let cl1 = List.map subs_crt_holes_ctx cl in
		            (* in case of success, put back the frame consisting of h2*h3 *)
		            let cl2 = List.map (fun x -> insert_ho_frame x (fun f -> CF.mkPhaseH f (CF.mkStarH h2 h3 pos) pos)) cl1 in
		            SuccCtx(cl2))
	      in

	      (*******************************************************)
	      (****** the second entailment uses h2 as lhs heap ******)
	      (*******************************************************)
	      (* push h3 as a continuation in the current ctx *)
	      let new_ctx = push_cont_ctx h3 ctx0 in
	      (* set the es_formula to h2 *)
	      let f_h2 = func h2 in
	      let wr_ctx = CF.set_context_formula new_ctx f_h2 in
	      Debug.devel_zprint (lazy ("heap_entail_split_lhs_phases: \ncall heap_entail_conjunct with lhs = writing phase\n")) pos;

	      (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)
	      (* let _ = print_string("split_lhs: entail using h2 = " ^ (Cprinter.string_of_h_formula h2) ^ "\n") in *)
	      (* let _ = print_string("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n") in *)


	      let (with_wr_ctx, with_wr_prf) = heap_entail_conjunct prog is_folding  wr_ctx conseq []  pos in
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
		            let cl = List.map subs_crt_holes_ctx cl in
		            (* put back the frame consisting of h1 and h3 *)
		            (* first add the frame []*h3 *) 
		            let cl = List.map (fun x -> insert_ho_frame x (fun f -> CF.mkStarH f h3 pos)) cl in
		            let cl = 
		              if not(consume_heap conseq) && not(drop_read_phase) then
			            (* next add the frame h1;[]*)
			            List.map (fun x -> insert_ho_frame x (fun f -> CF.mkPhaseH h1 f pos)) cl 
		              else
			            (* else drop the read phase (don't add back the frame) *)
			            let xpure_rd_0, _, _, memset_rd = xpure_heap 2 prog h1 0 in
			            let xpure_rd_1, _, _, memset_rd = xpure_heap 2 prog h1 1 in
			            (* add the pure info for the dropped reading phase *)
			            List.map 
			                (Cformula.transform_context 
			                    (fun es -> 
				                    Ctx{es with 
					                    (* add xpure0 directly to the state formula *)
					                    es_formula = mkStar es.es_formula (formula_of_mix_formula xpure_rd_0 pos) Flow_combine pos;
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
				            (* let _ = print_string("*******************************************") in *)
				            (* let _ = print_string("entailment uses the continuation\n") in *)
				            (* let _ = print_string("*******************************************") in *)
			                heap_entail_with_cont  prog is_folding  ctx0 conseq ft h1 h2 h3 with_wr_ctx with_wr_prf func drop_read_phase pos

	      in
	      (* union of states *)
	      (*	let _ = print_string("compute final answer\n") in*)
	      ((fold_context_left [with_rd_ctx; final_ctx]),( mkOrRight ctx0 conseq [with_rd_prf; final_prf]))		
		      (*  end of helper method *)

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
      Debug.no_2 "heap_entail_with_cont"
          (Cprinter.string_of_context)
          (fun _ -> "RHS")
          (* (Cprinter.string_of_formula) *)
          (fun _ -> "OUT")
          (fun ctx0 conseq -> heap_entail_with_cont_x prog is_folding  ctx0 conseq ft h1 h2 h3 with_wr_ctx with_wr_prf
              func drop_read_phase pos) ctx0 conseq

    (* handles the possible ent continuations *)
    and heap_entail_with_cont_x
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
        | ContinuationErr(fc) ->
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
	              let _, lhs = pop_cont_es lhs in
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
		              (Debug.devel_zprint (lazy ("heap_entail_split_lhs_phases: \ncall heap_entail_split_lhs_phase for the continuation\n")) pos;
		              heap_entail_split_lhs_phases prog is_folding  cont_ctx conseq drop_read_phase pos)
		            else
		              (Debug.devel_zprint (lazy ("heap_entail_split_lhs_phases: \ncall heap_entail_conjunct for the continuation\n")) pos;
		              heap_entail_conjunct prog is_folding  cont_ctx conseq [] pos)
	              in
		          (match after_wr_ctx with
		            | FailCtx _ -> (after_wr_ctx, after_wr_prf)
		            | SuccCtx (cl) -> 
		                  (* substitute the holes due to the temporary removal of matched immutable nodes *) 
		                  (* let _ = print_string("Substitute the holes\n") in *)
		                  let cl = List.map subs_crt_holes_ctx cl in
			              (* in case of success, put back the frame consisting of h1 and what's left of h2 *)
			              (* first add the frame h2_rest*[] *) 
		                  let cl = List.map (fun x -> insert_ho_frame x (fun f -> CF.mkStarH h2_rest f pos)) cl in
			              (* next add the frame h1;[]*)
		                  let cl =
			                if not(consume_heap conseq)  && not(drop_read_phase) then
			                  List.map (fun x -> insert_ho_frame x (fun f -> CF.mkPhaseH h1 f pos)) cl 
			                else
			                  (* drop read phase *)
			                  let xpure_rd_0, _, _, memset_rd = xpure_heap 3 prog h1 0 in
			                  let xpure_rd_1, _, _, memset_rd = xpure_heap 3 prog h1 1 in
			                  (* add the pure info corresponding to the dropped reading phase *)
			                  List.map 
			                      (Cformula.transform_context 
				                      (fun es -> 
				                          Ctx{es with 
					                          (* add xpure0 directly to the state formula *)
					                          es_formula = mkStar es.es_formula (formula_of_mix_formula xpure_rd_0 pos) Flow_combine pos;
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

		                let cl = List.map subs_crt_holes_ctx cl in   
		                (* in case of success, put back the frame consisting of h1;h2*[] *)
		                (* first add the frame h2*[] *) 
		                let cl = List.map (fun x -> insert_ho_frame x (fun f -> CF.mkStarH h2 f pos)) cl in
                        (* next add the frame h1;[]*)

		                let cl =
			              if not(consume_heap conseq)  && not(drop_read_phase) then
  				            List.map (fun x -> insert_ho_frame x (fun f -> CF.mkPhaseH h1 f pos)) cl
			              else
			                (* drop read phase *)
			                let xpure_rd_0, _, _, memset_rd = xpure_heap 3 prog h1 0 in
			                let xpure_rd_1, _, _, memset_rd = xpure_heap 3 prog h1 1 in
			                (* add the pure info corresponding to the dropped reading phase *)
			                List.map
			                    (Cformula.transform_context
				                    (fun es ->
				                        Ctx{es with
					                        (* add xpure0 directly to the state formula *)
					                        es_formula = mkStar es.es_formula (formula_of_mix_formula xpure_rd_0 pos) Flow_combine pos;
					                        (* store xpure_1 of the dropped phase for the case it is needed later during the entailment (i.e. xpure0 is not enough) *)
					                        es_aux_xpure_1 = MCP.merge_mems es.es_aux_xpure_1 xpure_rd_1 true;
					                    })) cl

		                in (SuccCtx(cl), with_wr_prf)
	            )
	          in (with_wr_ctx, with_wr_prf)
    in

    (* main method *)
    let lhs = CF.formula_of_context ctx0
    in
    match lhs with 
      | Base(bf) -> 
	        let (h, p, fl, b, t) = CF.split_components lhs in
	        helper_lhs h (fun xh -> CF.mkBase xh p t fl b pos)

      | Exists({formula_exists_qvars = qvars;
	    formula_exists_heap = h;
        formula_exists_pure = p;
        formula_exists_type = t;
        formula_exists_flow = fl;
        formula_exists_branches = b;
        formula_exists_label = l;
        formula_exists_pos = pos }) -> 
	        helper_lhs h (fun xh -> CF.mkExists qvars xh p t fl b pos)
      | _ -> report_error no_pos ("[solver.ml]: No disjunction on the LHS should reach this level\n")



(* check the entailment of two conjuncts  *)
(* return value: if fst res = true, then  *)
(* snd res is the residual. Otherwise     *)
(* snd res is the constraint that causes  *)
(* the check to fail.                     *)

and heap_entail_conjunct (prog : prog_decl) (is_folding : bool)  (ctx0 : context) (conseq : formula)
      (rhs_h_matched_set:CP.spec_var list) pos : (list_context * proof) =
  Debug.no_3_loop "heap_entail_conjunct" string_of_bool Cprinter.string_of_context Cprinter.string_of_formula
      (fun (c,_) -> Cprinter.string_of_list_context c)
      (fun  is_folding ctx0 c -> heap_entail_conjunct_x prog is_folding ctx0 c rhs_h_matched_set pos) is_folding ctx0 conseq

and heap_entail_conjunct_x (prog : prog_decl) (is_folding : bool)  (ctx0 : context) (conseq : formula) rhs_matched_set pos : (list_context * proof) =
  (* PRE : BOTH LHS and RHS are not disjunctive *)
  Debug.devel_zprint (lazy ("heap_entail_conjunct:"
  ^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx0)
  ^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq))) pos;
	(*print_string ("heap_entail_conjunct:"
      ^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx0)
      ^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq));*)
    (* <<<<<<< solver.ml *)
    (* print_string "start\n";flush(stdout); let r = *)
    heap_entail_conjunct_helper 3 prog is_folding  ctx0 conseq rhs_matched_set pos
        (*in print_string "stop\n";flush(stdout);r*)
        (* check the entailment of two conjuncts  *)
        (* return value: if fst res = true, then  *)
        (* snd res is the residual. Otherwise     *)
        (* snd res is the constraint that causes  *)
        (* the check to fail.                     *)

and heap_entail_conjunct_helper i (prog : prog_decl) (is_folding : bool)  (ctx0 : context) (conseq : formula)
      (rhs_h_matched_set:CP.spec_var list) pos : (list_context * proof) =
  let pr1 = Cprinter.string_of_context in
  let pr2 (r,_) = Cprinter.string_of_list_context r in
  Debug.no_1_num i "heap_entail_conjunct_helper" pr1 pr2
      (fun _ -> heap_entail_conjunct_helper_x (prog : prog_decl) (is_folding : bool)  (ctx0 : context) (conseq : formula)
          (rhs_h_matched_set:CP.spec_var list) pos) ctx0

and heap_entail_conjunct_helper_x (prog : prog_decl) (is_folding : bool)  (ctx0 : context) (conseq : formula)
      (rhs_h_matched_set:CP.spec_var list) pos : (list_context * proof) =
  Debug.devel_zprint (lazy ("heap_entail_conjunct_helper:"
  ^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx0)
  ^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq))) pos;
	(*print_string ("\nAn Hoa :: heap_entail_conjunct_helper:" ^ "\nContext:\n" ^ (Cprinter.string_of_context ctx0) ^ "\nConsequence:\n" ^ (Cprinter.string_of_formula conseq));*)
    match ctx0 with
      | OCtx _ -> report_error pos ("heap_entail_conjunct_helper: context is disjunctive or fail!!!")
      | Ctx estate -> begin
	      let ante = estate.es_formula in
		  (*let _ = print_string ("\nAN HOA CHECKPOINT :: Antecedent: " ^ (Cprinter.string_of_formula ante)) in*)
	      match ante with
	        | Exists ({formula_exists_qvars = qvars;
		      formula_exists_heap = qh;
		      formula_exists_pure = qp;
		      formula_exists_type = qt;
		      formula_exists_flow = qfl;
		      formula_exists_branches = qb;
		      formula_exists_pos = pos}) ->
                  (* let _ = print_endline "WN# :Exists" in *)
		          (* eliminating existential quantifiers from the LHS *)
		          (* ws are the newly generated fresh vars for the existentially quantified vars in the LHS *)
		          let ws = CP.fresh_spec_vars qvars in
		          (*--- 09.05.2008 *)
		          (*let _ = (print_string ("\n[solver.ml, line 1183]: fresh name = " ^ (Cprinter.string_of_spec_var_list ws) ^ "!!!!!!!!!!!\n")) in*)
		          (*09.05.2008 ---*)
                  (* TODO : for memo-pure, these fresh_vars seem to affect partitioning *)
		          let st = List.combine qvars ws in
		          let baref = mkBase qh qp qt qfl qb pos in
		          let new_baref = subst st baref in
		          (* new ctx is the new context after substituting the fresh vars for the exist quantified vars *)
		          let new_ctx = Ctx {estate with
				      es_formula = new_baref;
				      es_ante_evars = ws @ estate.es_ante_evars;
				      es_unsat_flag = false;} in
		          (* call the entailment procedure for the new context - with the existential vars substituted by fresh vars *)
		          let rs, prf1 = heap_entail_conjunct_helper 2 prog is_folding  new_ctx conseq rhs_h_matched_set pos in
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
                (* let _ = print_endline "WN# :_" in *)
		        match conseq with
		          | Exists ({formula_exists_qvars = qvars;
			        formula_exists_heap = qh;
			        formula_exists_pure = qp;
			        formula_exists_type = qt;
			        formula_exists_flow = qfl;
			        formula_exists_branches = qb;
			        formula_exists_pos = pos}) ->
		                (* quantifiers on the RHS. Keep them for later processing *)
		                let ws = CP.fresh_spec_vars qvars in
		                let st = List.combine qvars ws in
		                let baref = mkBase qh qp qt qfl qb pos in
		                let new_baref = subst st baref in
				        let new_ctx = Ctx {estate with es_evars = ws @ estate.es_evars} in
		                let tmp_rs, tmp_prf = heap_entail_conjunct_helper 1 prog is_folding  new_ctx new_baref rhs_h_matched_set pos in
			            (match tmp_rs with
			              | FailCtx _ -> (tmp_rs, tmp_prf)
			              | SuccCtx sl -> 
                                (* let _ = print_endline ("WN#4:"^(Cprinter.string_of_list_context tmp_rs)) in *)
			                    let prf = mkExRight ctx0 conseq qvars ws tmp_prf in
				                (*added 09-05-2008 , by Cristian, checks that after the RHS existential elimination the newly introduced variables will no appear in the residue hence no need to quantify*)
			                    let _ = List.map (redundant_existential_check ws) sl in
			                    let res_ctx =
				                  if !Globals.elim_exists then List.map elim_exists_ctx sl
				                  else sl in
                                let r = SuccCtx res_ctx in
                                (* let _ = print_endline ("WN#5:"^(Cprinter.string_of_list_context r)) in *)
				                (r, prf))
		          | _ ->
		                let h1, p1, fl1, br1, t1 = split_components ante in
		                let h2, p2, fl2, br2, t2 = split_components conseq in
			            (* let _ = print_string "pp 1\n" in*)
			            if (isAnyConstFalse ante)&&(CF.subsume_flow_ff fl2 fl1) then 
			              (* let _ = print_string ("got: "^(Cprinter.string_of_formula ante)^"|-"^(Cprinter.string_of_formula conseq)^"\n\n") in *)
			              (SuccCtx [false_ctx_with_flow_and_orig_ante estate fl1 ante pos], UnsatAnte)
			            else					  
			              (*  let _ = print_string "pp 2\n" in*)
			              (* let _ = print_string ("bol : "^(string_of_bool ((CF.is_false_flow fl2.formula_flow_interval)))^"\n") in*)
			              if (not(is_false_flow fl2.formula_flow_interval)) && not(CF.subsume_flow_ff fl2 fl1) then begin
			                Debug.devel_zprint (lazy ("heap_entail_conjunct_helper: "
						    ^ "conseq has an incompatible flow type"
						    ^ "\ncontext:\n"
						    ^ (Cprinter.string_of_context ctx0)
						    ^ "\nconseq:\n"
						    ^ (Cprinter.string_of_formula conseq))) pos;
                            (* TODO : change to meaningful msg *)
                            (* what if must failure on the ante -> conseq *)
                            if CF.overlap_flow_ff fl2 fl1 then
                              begin
                                let err_msg =
                                  if (CF.subsume_flow_f !error_flow_int fl1) then
                                    ("1.2: " ^ (exlist # get_closest fl1.CF.formula_flow_interval))
                                  else
                                    "1.2: conseq has an incompatible flow type"
                                in
                                (*let _ = print_endline ("locle 1:"^
                                  (exlist # get_closest fl1.CF.formula_flow_interval) ) in*)
                                let fe = mk_failure_may err_msg undefined_error in
                                let may_flow_failure =
			                      FailCtx (Basic_Reason ({fc_message = err_msg;
							      fc_current_lhs = estate;
							      fc_orig_conseq = struc_formula_of_formula conseq pos;
							      fc_prior_steps = estate.es_prior_steps;
							      fc_current_conseq = CF.formula_of_heap HFalse pos;
							      fc_failure_pts =[];}, fe)) in
                                (*set conseq with top flow, top flow is the highest flow.*)
                                let new_conseq = CF.substitute_flow_into_f !top_flow_int conseq in
                                let res,prf = heap_entail_conjunct prog is_folding ctx0 new_conseq rhs_h_matched_set pos in
                                (and_list_context may_flow_failure res, prf)
                              end
                            else
                              let err_msg,fe =
                                if CF.subsume_flow_f !error_flow_int fl1 then
                                 (* let _ = print_endline ("\ntodo:" ^ (Cprinter.string_of_flow_formula "" fl1)) in*)
                                  let err_name = (exlist # get_closest fl1.CF.formula_flow_interval) in
                                  let err_msg = "1.1: " ^ err_name in
                                  (err_msg,
                                  mk_failure_must err_msg err_name)
                                else
                                  let err_name = "conseq has an incompatible flow type" in
                                  let err_msg = "1.1: " ^ err_name in
                                  (err_msg,
                                  mk_failure_must err_msg undefined_error)
                              in
                              (*let _ = print_endline ("locle 2:"^
                                (exlist # get_closest fl1.CF.formula_flow_interval) ) in*)
			                  (CF.mkFailCtx_in (Basic_Reason ({fc_message =err_msg;
							  fc_current_lhs = estate;
							  fc_orig_conseq = struc_formula_of_formula conseq pos;
							  fc_prior_steps = estate.es_prior_steps;
							  fc_current_conseq = CF.formula_of_heap HFalse pos;
							  fc_failure_pts =[];}, fe)), UnsatConseq)
			              end
			              else
			                match h2 with
			                  | HFalse (* -> (--[], UnsatConseq)  entailment fails *)
			                  | HTrue -> begin
				                  Debug.devel_zprint (lazy ("heap_entail_conjunct_helper: "
						          ^ "conseq has an empty heap component"
						          ^ "\ncontext:\n"
						          ^ (Cprinter.string_of_context ctx0)
						          ^ "\nconseq:\n"
						          ^ (Cprinter.string_of_formula conseq))) pos;
				                  let b1 = { formula_base_heap = h1;
					              formula_base_pure = p1;
					              formula_base_type = t1;
					              formula_base_flow = fl1;
					              formula_base_branches = br1;
					              formula_base_label = None;
					              formula_base_pos = pos } in
				                  (* 23.10.2008 *)
				                  (*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
				                  (* at the end of an entailment due to the epplication of an universal lemma, we need to move the explicit instantiation to the antecedent  *)
				                  (* Remark: for universal lemmas we use the explicit instantiation mechanism,  while, for the rest of the cases, we use implicit instantiation *)
				                  (*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                                  (*LDK: remove duplicated conj from the p2*)
                                  let p2 = remove_dupl_conj_eq_mix_formula p2 in
				                  let ctx, proof = heap_entail_empty_rhs_heap prog is_folding  estate b1 p2 br2 pos in
				                  (* let new_ctx = *)
				                  (*   if  then ((\*print_string ("YES Expl inst!!\n");*\) move_lemma_expl_inst_ctx_list ctx p2) *)
				                  (*   else ((\*print_string ("NO Expl inst!!\n");*\) ctx ) *)
				                  (* in *)
                                  (* explicit instantiation
                                     this will move some constraint to the LHS*)
                                  (*LDK: 25/08/2011, also instatiate ivars*)                          
                                  (*this move_expl_inst call can occur at the end of folding and also 
                                    at the end of entailments of stages possibly leading to duplications of instantiations
                                    moving it would require the rhs pure to be moved as well...*)                          

				                  (* let new_ctx = move_expl_inst_ctx_list ctx p2 in *)
  				                  let new_ctx =
    						        (* let _ = print_endline ("Cris: ctx = " ^ (Cprinter.string_of_list_context ctx) ^ "\n") in *)
						            (* when reaching the last phase of the entailment, we can move the explicit instantiations to the lhs; otherwise keep them in the aux consequent *)
						            (match ctx with
						  	          | FailCtx _ -> ctx
						  	          | SuccCtx cl ->
						  	                let new_cl =
						  	                  List.map (fun c ->
						  	                      (transform_context
    						  		                  (fun es ->
						  		                          (* explicit inst *)
						  		                          let l_inst = get_expl_inst es p2 in
						  		                          let es = move_impl_inst_estate es p2 in
						  		                          Ctx ( if (es.es_imm_last_phase) then
						  		      	                    move_expl_inst_estate es p2
						  		                          else
						  			                        add_to_aux_conseq_estate es (MCP.pure_of_mix l_inst) pos)
						  		                      ) c)) cl
						  	                in SuccCtx(new_cl))

						    
						  in


				                  (new_ctx, proof)
				                end
			                  | _ -> begin 
				                  Debug.devel_zprint (lazy ("heap_entail_conjunct_helper: "
						          ^ "conseq has an non-empty heap component"
						          ^ "\ncontext:\n"
						          ^ (Cprinter.string_of_context ctx0)
						          ^ "\nconseq:\n"
						          ^ (Cprinter.string_of_formula conseq))) pos;
				                  let b1 = { formula_base_heap = h1;
					              formula_base_pure = p1;
					              formula_base_type = t1;
					              formula_base_branches = br1;
					              formula_base_flow = fl1;
					              formula_base_label = None;
					              formula_base_pos = pos } in
				                  let b2 = { formula_base_heap = h2;
					              formula_base_pure = p2;
					              formula_base_type = t2;
					              formula_base_flow = fl2;
					              formula_base_branches = br2;
					              formula_base_label = None;
					              formula_base_pos = pos } in
				                  heap_entail_non_empty_rhs_heap prog is_folding  ctx0 estate ante conseq b1 b2 rhs_h_matched_set pos
				                end
	          end
        end

and heap_entail_build_mix_formula_check_a (evars : CP.spec_var list) (ante : MCP.mix_formula) (conseq : MCP.mix_formula) pos : (MCP.mix_formula * MCP.mix_formula) =
  (* let _ = print_string ("An Hoa :: heap_entail_build_mix_formula_check :: INPUTS\n" ^ *)
  (* "EXISTENTIAL VARIABLES = " ^ (String.concat "," (List.map Cprinter.string_of_spec_var evars)) ^ "\n" ^ *)
  (* "ANTECEDENT = " ^ (Cprinter.string_of_mix_formula ante) ^ "\n" ^ *)
  (* "CONSEQUENCE = " ^ (Cprinter.string_of_mix_formula conseq)  ^ "\n") in   *)
  let avars = mfv ante in
  let sevars = (* List.map CP.to_int_var *) evars in
  let outer_vars, inner_vars = List.partition (fun v -> CP.mem v avars) sevars in
  (* let _ = print_string ("\nheap_entail_build_mix_formula_check: conseq: "^(Cprinter.string_of_mix_formula conseq)) in *)
  let conseq = if !no_RHS_prop_drop then conseq else  MCP.mix_cons_filter conseq MCP.isImplT in
  (* let _ = print_string ("\nheap_entail_build_mix_formula_check: conseq: "^(Cprinter.string_of_mix_formula conseq)) in *)
  let tmp1 = (*MCP.memo_pure_push_exists*) elim_exists_mix_formula inner_vars conseq no_pos in
  (* let _ = print_string ("\nheap_entail_build_mix_formula_check: tmp1: "^(Cprinter.string_of_mix_formula tmp1)) in *)
  let tmp1 = MCP.memo_pure_push_exists outer_vars tmp1 in
  (ante,tmp1)

and heap_entail_build_mix_formula_check (evars : CP.spec_var list) (ante : MCP.mix_formula) (conseq : MCP.mix_formula) pos : (MCP.mix_formula * MCP.mix_formula) =
  let pr = Cprinter.string_of_mix_formula in
  Debug.no_3 "heap_entail_build_mix_formula_check"  (fun l -> Cprinter.string_of_spec_var_list l) 
      pr pr (pr_pair pr pr)
      ( fun c1 ante c2 -> heap_entail_build_mix_formula_check_a c1 ante c2 pos) evars ante conseq       

and heap_entail_build_pure_check ev an cq pos =
  Debug.no_1 "heap_entail_build_pure_check" 
      Cprinter.string_of_pure_formula 
      (fun (f1,f2) -> "f1 = " ^ (Cprinter.string_of_pure_formula f1) ^ "; f2 = " ^ (Cprinter.string_of_pure_formula f2) ^ "\n") 
      (fun cq -> heap_entail_build_pure_check_a ev an cq pos) cq

and heap_entail_build_pure_check_a (evars : CP.spec_var list) (ante : CP.formula) (conseq : CP.formula) pos : (CP.formula * CP.formula) =
  let tmp1 = CP.mkExists evars conseq None no_pos in
  (ante, tmp1)
	  
and xpure_imply (prog : prog_decl) (is_folding : bool)   lhs rhs_p timeout : bool = 
  let pr1 = Cprinter.string_of_entail_state in
  let pr2 = Cprinter.string_of_pure_formula in
  Debug.no_2 "xpure_imply" pr1 pr2 string_of_bool
      (fun _ _ -> xpure_imply_x (prog : prog_decl) (is_folding : bool)   lhs rhs_p timeout) lhs rhs_p

and xpure_imply_x (prog : prog_decl) (is_folding : bool)   lhs rhs_p timeout : bool = 
  let imp_subno = ref 0 in
  let estate = lhs in
  let pos = no_pos in
  let r,c = match lhs.es_formula with
    | Or _ -> report_error no_pos ("xpure_imply: encountered Or formula on lhs")
    | Base b ->  (b,lhs)
    | Exists b ->  report_error no_pos ("xpure_imply: encountered Exists formula on lhs")in
  let lhs_h = r.formula_base_heap in  
  let lhs_p = r.formula_base_pure in
  let lhs_b = r.formula_base_branches in
  let _ = reset_int2 () in
  let xpure_lhs_h, xpure_lhs_h_b, _, memset = xpure_heap 4 prog (mkStarH lhs_h estate.es_heap pos) 1 in
  let tmp1 = MCP.merge_mems lhs_p xpure_lhs_h true in
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

(*maximising must bug with RAND (error information)*)
and check_maymust_failure (ante:CP.formula) (cons:CP.formula): (CF.failure_kind*((CP.formula*CP.formula) list * (CP.formula*CP.formula) list * (CP.formula*CP.formula) list))=
  let pr1 = Cprinter.string_of_pure_formula in
  let pr3 = pr_list (pr_pair pr1 pr1) in
  let pr2 = pr_pair (Cprinter.string_of_failure_kind) (pr_triple pr3 pr3 pr3) in
  Debug.no_2 "check_maymust_failure" pr1 pr1 pr2 (fun _ _ -> check_maymust_failure_x ante cons) ante cons

(*maximising must bug with RAND (error information)*)
and check_maymust_failure_x (ante:CP.formula) (cons:CP.formula): (CF.failure_kind*((CP.formula*CP.formula) list * (CP.formula*CP.formula) list * (CP.formula*CP.formula) list))=
  if not !disable_failure_explaining then
    let r = ref (-9999) in
    let is_sat f = TP.is_sat_sub_no f r in
    let find_all_failures a c = CP.find_all_failures is_sat a c in
    let find_all_failures a c =
      let pr1 = Cprinter.string_of_pure_formula in
      let pr2 = pr_list (pr_pair pr1 pr1) in
      let pr3 = pr_triple pr2 pr2 pr2 in
      Debug.no_2 "find_all_failures" pr1 pr1 pr3 find_all_failures a c in
    let filter_redundant a c = CP.simplify_filter_ante TP.simplify_always a c in
    (* Check MAY/MUST: if being invalid and (exists (ante & conseq)) = true then that's MAY failure,
       otherwise MUST failure *)
    let ante_filter = filter_redundant ante cons in
    let (r1, r2, r3) = find_all_failures ante_filter cons in
    if List.length (r1@r2) = 0 then
      begin
        (CF.mk_failure_may_raw "", (r1, r2, r3))
      end
    else
      begin
        (*compute lub of must bug and current fc_flow*)
        (CF.mk_failure_must_raw "", (r1, r2, r3))
      end
  else
    (CF.mk_failure_may_raw "", ([], [], [(ante, cons)]))

and build_and_failures i (failure_code:string) (failure_name:string) ((contra_list, must_list, may_list)
    :((CP.formula*CP.formula) list * (CP.formula*CP.formula) list * (CP.formula*CP.formula) list)) 
      (fail_ctx_template: fail_context): list_context=
  let pr1 = Cprinter.string_of_pure_formula in
  let pr3 = pr_list (pr_pair pr1 pr1) in
  let pr4 = pr_triple pr3 pr3 pr3 in
  let pr2 = (fun _ -> "OUT") in
  Debug.no_1_num i "build_and_failures" pr4 pr2 
      (fun triple_list -> build_and_failures_x failure_code failure_name triple_list fail_ctx_template)
      (contra_list, must_list, may_list)

(*maximising must bug with AND (error information)*)
(* to return fail_type with AND_reason *)
and build_and_failures_x (failure_code:string) (failure_name:string) ((contra_list, must_list, may_list)
    :((CP.formula*CP.formula) list * (CP.formula*CP.formula) list * (CP.formula*CP.formula) list)) (fail_ctx_template: fail_context): list_context=
  if not !disable_failure_explaining then
    let build_and_one_kind_failures (failure_string:string) (fk: CF.failure_kind) (failure_list:(CP.formula*CP.formula) list):CF.fail_type option=
      (*build must/may msg*)
      let build_failure_msg (ante, cons) =
        let ll = (CP.list_pos_of_formula ante []) @ (CP.list_pos_of_formula cons []) in
        (*let _ = print_endline (Cprinter.string_of_list_loc ll) in*)
        let lli = CF.get_lines ll in
        (*possible to eliminate unnecessary intermediate that are defined by equality.*)
        (*not sure it is better*)
        let ante = CP.elim_equi_ante ante cons in
        ((Cprinter.string_of_pure_formula ante) ^ " |- "^
        (Cprinter.string_of_pure_formula cons) ^ ". LOCS:[" ^ (Cprinter.string_of_list_int lli) ^ "]", ll) in
      match failure_list with
        | [] -> None
        | _ ->
            let strs,locs= List.split (List.map build_failure_msg failure_list) in
            (*get line number only*)
            let rec get_line_number ll rs=
              match ll with
                | [] -> rs
                | l::ls -> get_line_number ls (rs @ [l.start_pos.Lexing.pos_lnum])
            in
            (*shoudl use ll in future*)
           (* let ll = Gen.Basic.remove_dups (get_line_number (List.concat locs) []) in*)
              let msg =
                match strs with
                  | [] -> ""
                  | [s] -> s ^ " ("  ^ failure_string ^ ")"
                  | _ -> (* "(failure_code="^failure_code ^ ") AndR[" ^ *)
                      "AndR[" ^ (String.concat "; " strs) ^ " ("  ^ failure_string ^ ").]"
              in
              let fe = match fk with
                |  Failure_May _ -> mk_failure_may msg failure_name
                | Failure_Must _ -> (mk_failure_must msg failure_name)
                | _ -> {fe_kind = fk; fe_name = failure_name ;fe_locs=[]}
              in
              Some (Basic_Reason ({fail_ctx_template with fc_message = msg }, fe))
    in
    let contra_fail_type = build_and_one_kind_failures "RHS: contradiction" (Failure_Must "") contra_list in
    let must_fail_type = build_and_one_kind_failures "must-bug" (Failure_Must "") must_list in
    let may_fail_type = build_and_one_kind_failures "may-bug" (Failure_May "") may_list in
    (*
      let pr oft =
      match oft with
      | Some ft -> Cprinter.string_of_fail_type ft
      | None -> "None"
      in
      let _ = print_endline ("locle contrad:" ^ (pr contra_fail_type)) in
      let _ = print_endline ("locle must:" ^ (pr must_fail_type)) in
      let _ = print_endline ("locle may:" ^ (pr may_fail_type)) in
    *)
    let oft = List.fold_left CF.mkAnd_Reason contra_fail_type [must_fail_type; may_fail_type] in
    match oft with
      | Some ft -> FailCtx ft
      | None -> (*report_error no_pos "Solver.build_and_failures: should be a failure here"*)
            let msg =  "use different strategies in proof searching (slicing)" in
            let fe =  mk_failure_may msg failure_name in
            FailCtx (Basic_Reason ({fail_ctx_template with fc_message = msg }, fe))
  else
    let msg = "failed in entailing pure formula(s) in conseq" in
    CF.mkFailCtx_in (Basic_Reason ({fail_ctx_template with fc_message = msg }, mk_failure_may msg failure_name))

(** An Hoa : Extract the relations that appears in the input formula
    *  RETURN : a list of b_formula, each of which is a RelForm  
*)
and extract_relations (f : CP.formula) : (CP.b_formula list) =
  match f with
	| CP.BForm (b, _) -> (let (p, _) = b in match p with
		| CP.RelForm _ -> [b]
		| _ -> [])
	| CP.And (f1, f2,_) -> (extract_relations f1) @ (extract_relations f2)
	| _ -> [] (* Or, Not, Exists, Forall contains "negative" information! *)

(** An Hoa : Extract equalities in a formula so that we can check identity latter.
    *  RETURN : A formula of a big conjunction /\ (e1 = e2).
*)
and extract_equality (f : CP.formula) : CP.formula =
  match f with
	| CP.BForm (b, _) -> (let (p, _) = b in match p with
		| CP.Eq _ -> f 
		| _ -> CP.mkTrue no_pos)
	| CP.And (f1, f2, _) -> CP.mkAnd (extract_equality f1) (extract_equality f2) no_pos
	| _ -> CP.mkTrue no_pos

(** An Hoa : Check if two expressions are exactly identical.
    *  RETURN : true/false
*)
and is_identical (exp1 : CP.exp) (exp2 : CP.exp) : bool =
  match exp1 with
    | CP.Var (CP.SpecVar (t1,vn1,p1),_) -> (match exp2 with
		| CP.Var (CP.SpecVar (t2,vn2,p2),_) -> vn1 = vn2 && p1 = p2
		| _ -> false)
	| CP.IConst (c1,_) -> (match exp2 with
		| CP.IConst (c2,_) -> c1 = c2
		| _ -> false)
	| CP.FConst (c1,_) -> (match exp2 with
		| CP.FConst (c2,_) -> c1 = c2
		| _ -> false)
	| _ -> false

(** An Hoa : Check if two expressions are exactly identical
    *           with respect to a collection of equality constraints.
    *  RETURN : true/false
*)
and is_relative_identical (eqctr : CP.formula) (exp1 : CP.exp) (exp2 : CP.exp) : bool =
  (is_identical exp1 exp2) || let res,_,_ = TP.imply eqctr (CP.mkEqExp exp1 exp2 no_pos) "" true None in res
	                                                                                                         
(** An Hoa : Construct a formula of form /\ (v = e) for v in vars, e being terms
    over the free variables in lhs.
    RETURN : a formula
*)
and pure_match (vars : CP.spec_var list) (lhs : MCP.mix_formula) (rhs : MCP.mix_formula) : CP.formula =
  let lhs = MCP.fold_mix_lst_to_lst lhs true true true in
  let rhs = MCP.fold_mix_lst_to_lst rhs true true true in
  let rl = List.concat (List.map extract_relations lhs) in (* Relations in LHS *)
  let rr = List.concat (List.map extract_relations rhs) in (* Relations in RHS *)
  (*let fl = CP.fv lhs in Free variables in LHS, assume that fl intersects vars is empty *)
  let pr = List.flatten (List.map (fun x -> List.map (fun y -> (x,y)) rr) rl) in (* Cartesian product of rl and rr. *)
  let eqctr = extract_equality (CP.conj_of_list lhs no_pos) in
  (*let _ = print_string "pure_match :: pairs of relations found : \n" in
	let _ = List.map (fun (x,y) -> print_string ("(" ^ Cprinter.string_of_b_formula x ^ "," ^ Cprinter.string_of_b_formula y ^ "\n")) pr in*)
  (* Internal function rel_match to perform matching of two relations *)
  let rel_match  (vars : CP.spec_var list) (rpair : CP.b_formula * CP.b_formula) : CP.formula =
	let (r1, _) = fst rpair in
	let (r2, _) = snd rpair in
	(*let _ = print_string ("rel_match :: on " ^ "{" ^ Cprinter.string_of_b_formula r1 ^ "," ^ Cprinter.string_of_b_formula r2 ^ "}\n") in*)
	(match r1 with
	  | CP.RelForm (rn1, args1, _) -> (match r2 with
		  | CP.RelForm (rn2, args2, _) -> (* TODO Implement *) 
				if (CP.eq_spec_var rn1 rn2) then
				  (* If the arguments at non-vars positions matched*)
				  (* then we add the args1[i] = args2[i] where *)
				  (* args2[i] should be a variable in vars *)
				  let correspondences = List.map2 (fun x y -> match y with 
					| CP.Var (s,_) -> if (List.mem s vars) then true 
					  else is_relative_identical eqctr x y 
					| _ -> is_relative_identical eqctr x y) args1 args2 in
				  (*let _ = List.map (fun x -> print_string ((string_of_bool x) ^ " , ")) correspondences in
					let _ = print_string " --> " in*) 
				  let matched_nonvars = List.fold_left (&&) true correspondences in
				  if matched_nonvars then (* Make a big conjunction of args1[i] = args2[i] *)
					(*let _ = print_string "Relation matched! " in*)
					let result = List.fold_left (fun x y -> CP.mkAnd x y no_pos) 
					  (CP.mkTrue no_pos)
					  (List.map2 (fun x y -> CP.mkEqExp x y no_pos) args1 args2) in
					(*let _ = print_string ("Result binding : " ^ (Cprinter.string_of_pure_formula result) ^ "\n") in*)
					result
				  else
					CP.mkTrue no_pos (* Some arguments does not fit, no constraint *)
				else  
				  (* Two relations of different names => no constraint between the arguments *)
				  CP.mkTrue no_pos
		  | _ -> failwith ("rel_match :: input should be a relation formula!"))
	  | _ -> failwith ("rel_match :: input should be a relation formula!")) (* End of internal function rel_match *) in 
  let match_conditions = List.map (rel_match vars) pr in (* Matches conditions are in m, just take a big conjunction of pr *)
  List.fold_left (fun x y -> CP.mkAnd x y no_pos) (CP.mkTrue no_pos) match_conditions
      (* End of pure_match *)


(* Termination: Try to prove rhs_wf with inference *)
(* rhs_wf = None --> measure succeeded *)
(* lctx = Fail --> well-founded termination failure *)
(* lctx = Succ --> termination succeeded with inference *)
and heap_infer_decreasing_wf_x prog estate rank is_folding lhs rhs_p_br pos =
  let lctx, _ = heap_entail_empty_rhs_heap prog is_folding estate lhs (MCP.mix_of_pure rank) rhs_p_br pos 
  in CF.estate_opt_of_list_context lctx

and heap_infer_decreasing_wf prog estate rank is_folding lhs rhs_p_br pos =
  let pr = !CP.print_formula in
  Debug.no_1 "heap_infer_decreasing_wf" pr pr_no
      (fun _ -> heap_infer_decreasing_wf_x prog estate rank is_folding lhs rhs_p_br pos) rank


and heap_entail_empty_rhs_heap p i_f es lhs rhs rhsb pos =
  let pr (e,_) = Cprinter.string_of_list_context e in
  Debug.no_3 "heap_entail_empty_rhs_heap" Cprinter.string_of_entail_state (fun c-> Cprinter.string_of_formula(Base c)) Cprinter.string_of_mix_formula pr
      (fun _ _ _ -> heap_entail_empty_rhs_heap_x p i_f es lhs rhs rhsb pos) es lhs rhs

and heap_entail_empty_rhs_heap_x (prog : prog_decl) (is_folding : bool)  estate_orig lhs (rhs_p:MCP.mix_formula) rhs_p_br pos : (list_context * proof) =
  (* An Hoa note: RHS has no heap so that we only have to consider whether "pure of LHS" |- RHS *)
  (* let _ = print_string ("\n\nAn Hoa :: heap_entail_empty_rhs_heap :: INPUTS\n" ^ *)
  (* "ENTAIL STATE = " ^ (Cprinter.string_of_estate estate) ^ "\n" ^ *)
  (* "LHS = " ^ (Cprinter.string_of_formula (Base lhs)) ^ "\n" ^ *)
  (* "RHS = " ^ (Cprinter.string_of_mix_formula rhs_p) ^ "\n\n") in *)
  let imp_subno = ref 1 in
  let lhs_h = lhs.formula_base_heap in
  let lhs_p = lhs.formula_base_pure in
  let lhs_t = lhs.formula_base_type in
  let lhs_fl = lhs.formula_base_flow in
  let lhs_b = lhs.formula_base_branches in
  (*TO CHECK: this may affect our current strategy*)
  (* An Hoa : INSTANTIATION OF THE EXISTENTIAL VARIABLES! *)
  let evarstoi = estate_orig.es_gen_expl_vars in
  let lhs_p = if (evarstoi = []) then (* Nothing to instantiate *) lhs_p 
  else (*let _ = print_endline ("\n\nheap_entail_empty_rhs_heap_x : Variables to be instantiated : " ^ (String.concat "," (List.map Cprinter.string_of_spec_var evarstoi))) in*)
			(* Temporarily suppress output of implication checking *)
			let _ = Smtsolver.suppress_all_output () in
			let _ = Tpdispatcher.push_suppress_imply_output_state () in
	 		let _ = Tpdispatcher.suppress_imply_output () in
	 		let inst = pure_match evarstoi lhs_p rhs_p in (* Do matching! *)
            let lhs_p = MCP.memoise_add_pure_N lhs_p inst in 
			(* Unsuppress the printing *)
	 		let _ = Smtsolver.unsuppress_all_output ()  in
	 		let _ = Tpdispatcher.restore_suppress_imply_output_state () in
 	 		(*let _ = print_string ("An Hoa :: New LHS with instantiation : " ^ (Cprinter.string_of_mix_formula lhs_p) ^ "\n\n") in*)
	 		lhs_p
  in
  (* An Hoa : END OF INSTANTIATION *)
  let _ = reset_int2 () in
  let curr_lhs_h = (mkStarH lhs_h estate_orig.es_heap pos) in
  let xpure_lhs_h0, xpure_lhs_h0_b, _, memset = xpure_heap 5 prog curr_lhs_h 0 in
  let xpure_lhs_h1, xpure_lhs_h1_b, _, memset = xpure_heap 5 prog curr_lhs_h 1 in
  (* add the information about the dropped reading phases *)
  let xpure_lhs_h1 = MCP.merge_mems xpure_lhs_h1 estate_orig.es_aux_xpure_1 true in
  let xpure_lhs_h1 = if (Cast.any_xpure_1 prog curr_lhs_h) then xpure_lhs_h1 else MCP.mkMTrue no_pos in
  (* let estate = estate_orig in *)
  let (estate,lhs_new,rhs_p,rhs_p_br) = Inf.infer_collect_rel TP.is_sat_raw estate_orig xpure_lhs_h1 
    lhs_p rhs_p rhs_p_br heap_entail_build_mix_formula_check pos in
  (* Termination *)
  let (estate,_,rhs_p,rhs_wf) = Term.check_term_rhs estate lhs_p xpure_lhs_h0 xpure_lhs_h1 rhs_p pos in
  (* Termination: Try to prove rhs_wf with inference *)
  (* rhs_wf = None --> measure succeeded or no striggered inference *)
  (* lctx = Fail --> well-founded termination failure - No need to update term_res_stk *)
  (* lctx = Succ --> termination succeeded with inference *)
  let estate = match rhs_wf with
  | None -> estate 
  | Some rank ->
      begin
        match (heap_infer_decreasing_wf prog estate rank is_folding lhs rhs_p_br pos) with
          | None ->     
              let t_ann, ml, il = Term.find_lexvar_es estate in
              let term_pos, t_ann_trans, orig_ante, _ = Term.term_res_stk # top in
              let term_measures, term_res, term_stack =
                Some (Fail TermErr_May, ml, il),
                (term_pos, t_ann_trans, orig_ante, 
                  Term.MayTerm_S (Term.Not_Decreasing_Measure t_ann_trans)),
                  (Term.string_of_term_res (term_pos, t_ann_trans, None, 
                  Term.TermErr (Term.Not_Decreasing_Measure t_ann_trans)))::estate.CF.es_var_stack
              in
              Term.term_res_stk # pop;
              Term.term_res_stk # push term_res;
              { estate with 
                 CF.es_var_measures = term_measures;
                 CF.es_var_stack = term_stack; 
              }
          | Some es -> es
      end
  in
  let stk_inf_pure = new Gen.stack in (* of xpure *)
  let stk_estate = new Gen.stack in (* of estate *)
  Debug.devel_zprint (lazy ("heap_entail_empty_heap: ctx:\n" ^ (Cprinter.string_of_estate estate))) pos;
  Debug.devel_zprint (lazy ("heap_entail_empty_heap: rhs:\n" ^ (Cprinter.string_of_mix_formula rhs_p))) pos;
  let fold_fun_impt (is_ok,succs,fails, (fc_kind,(contra_list, must_list, may_list))) ((branch_id, rhs_p):string*MCP.mix_formula) =
	begin
      if (is_ok = false) then (is_ok,succs,fails, (fc_kind,(contra_list, must_list, may_list))) 
      else
        let m_lhs = MCP.combine_mix_branch branch_id (lhs_new, lhs_b) in
        let tmp2 = MCP.merge_mems m_lhs (MCP.combine_mix_branch branch_id (xpure_lhs_h0, xpure_lhs_h0_b)) true in
        let tmp3 = MCP.merge_mems m_lhs (MCP.combine_mix_branch branch_id (xpure_lhs_h1, xpure_lhs_h1_b)) true in
        let exist_vars = estate.es_evars@estate.es_gen_expl_vars@estate.es_ivars(* @estate.es_gen_impl_vars *) in
        let new_ante0, new_conseq0 = heap_entail_build_mix_formula_check exist_vars tmp2 rhs_p pos in
        let new_ante1, new_conseq1 = heap_entail_build_mix_formula_check exist_vars tmp3 rhs_p pos in

	    (* let _ = print_string ("An Hoa :: heap_entail_empty_rhs_heap :: After heap_entail_build_mix_formula_check\n" ^ *)
	    (* "NEW ANTECEDENT = " ^ (Cprinter.string_of_mix_formula new_ante0) ^ "\n" ^ *)
	    (* "NEW CONSEQUENCE = " ^ (Cprinter.string_of_mix_formula new_conseq0)  ^ "\n") in *)


	    (* 26.03.2009 simplify the pure part *)
	    (*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
	    (* TODO: if xpure 1 is needed, then perform the same simplifications as for xpure 0 *)
	    (*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
        let new_ante0 =
          if!omega_simpl && not(TP.is_mix_bag_constraint new_ante0)&& not(TP.is_mix_list_constraint new_ante0)
          then
            let simp_ante = new_ante0 in
            if !omega_err = false
            then simp_ante
            else (omega_err := false; new_ante0)	(* reset the error flag *)
          else new_ante0
        in
        let new_conseq0 =
	      if !omega_simpl && not(TP.is_mix_bag_constraint new_conseq0)&&
            not(TP.is_mix_list_constraint new_conseq0) then
              begin
	            let simp_conseq = (Debug.devel_zprint (lazy ("simplify the consequent with omega")) no_pos;
		        (*simpl_memo_pure_formula*) new_conseq0) in
	            let simp_conseq1 =  if !omega_err = false
                then simp_conseq
                else (omega_err := false; new_conseq0)
                in
                (* use the previous conseq , reset the error flag *)
                memo_normalize_to_CNF_new (MCP.memo_arith_simplify simp_conseq1) pos
              end
	      else new_conseq0
        in
        let split_conseq = (*Tpdispatcher.split_conjunctions*) new_conseq0 in
        let split_ante0 = (*Tpdispatcher.split_disjunctions*) new_ante0 in
        let split_ante1 = new_ante1 in
        (* let lhs_xpure = split_ante1 in *)
        (* let rhs_xpure = split_conseq in *)
        (* match ip1 with *)
        (*   | Some(es,p) -> *)
        (*   | None -> *)
        (* let _ = print_endline ("WN: new_conseq0"^(Cprinter.string_of_mix_formula new_conseq0)) in *)
        (*^ "." ^ (string_of_int !imp_subno) ^ " with XPure0"*) 
	    (* <<<<<<< solver.ml *)
	    (*       let split_conseq = Tpdispatcher.split_conjunctions new_conseq0 in *)
	    (*       let split_ante0 = Tpdispatcher.split_disjunctions new_ante0 in *)
	    (*       let split_ante1 = Tpdispatcher.split_disjunctions new_ante in *)
	    (* 	  (\* first try for xpure 0 and see what conjuncts can be discharged *\) *)
	    (*       let res1,res2,res3 = if (CP.isConstTrue rhs_p) then (true,[],None) else (imply_conj split_ante0 split_ante1 split_conseq memset) in	 *)
	    (* 	  (\* added by cezary  for branches *\) *)
	    (*       let res1,res2,re3 =  *)
	    (* ======= *)
        let i_res1,i_res2,i_res3 = 
          if (MCP.isConstMTrue rhs_p)  then (true,[],None)
		  else let _ = Debug.devel_pprint ("IMP #" ^ (string_of_int !imp_no)) no_pos in
          (imply_mix_formula split_ante0 split_ante1 split_conseq imp_no memset) 
        in
        let i_res1,i_res2,i_res3 =
          if i_res1==true then (i_res1,i_res2,i_res3)
          else 
            let (ip1,ip2) = Inf.infer_pure_m estate split_ante1 split_ante0 split_conseq pos in
            begin
              match ip1 with
                | Some(es,p) -> 
                      stk_inf_pure # push p;
                      stk_estate # push es;
                      (true,[],None)
                | None ->
                      begin
                        match ip2 with
                          | None -> i_res1,i_res2,i_res3
                          | Some pf ->
                                stk_inf_pure # push pf;
                                let new_pf = MCP.mix_of_pure pf in
                                let split_ante0 = MCP.merge_mems split_ante0 new_pf true in 
                                let split_ante1 = MCP.merge_mems split_ante1 new_pf true in
                                let _ = Debug.devel_pprint ("IMP #" ^ (string_of_int !imp_no)) no_pos in
                                (imply_mix_formula split_ante0 split_ante1 split_conseq imp_no memset)
                      end
            end in
        let res1,res2,re3, (fn_fc_kind, (fn_contra_list, fn_must_list, fn_may_list)) =
          if i_res1 = false && branch_id = "" then
            begin
              let (new_fc_kind, (new_contra_list, new_must_list, new_may_list)) =
                (*check_maymust: maximising must bug with AND (error information)*)
                let cons4 = (MCP.pure_of_mix split_conseq) in
                (* Check MAY/MUST: if being invalid and (exists (ante & conseq)) = true then that's MAY failure,
                   otherwise MUST failure *)
                (*check maymust for ante0*)
                let (fc, (contra_list, must_list, may_list)) = check_maymust_failure (MCP.pure_of_mix split_ante0) cons4 in
                match fc with
                  | Failure_May _ ->
                        begin
                          (*check maymust for ante1*)
                          let (fc, (contra_list, must_list, may_list)) = check_maymust_failure (MCP.pure_of_mix split_ante1) cons4 in
                          (
                              (fc, (contra_list, must_list, may_list))
                          )
                        end
                  | _ ->
                        begin
                          (fc, (contra_list, must_list, may_list))
                        end
              in
	          let branches = Gen.BList.remove_dups_eq (=) (List.map (fun (bid, _) -> bid) (xpure_lhs_h1_b @ lhs_b)) in
              let fold_fun (is_ok,a2,a3, (bug_kind, (contra_list1, must_list1, may_list1))) branch_id_added =
                if is_ok then (is_ok,a2,a3, (bug_kind, (contra_list1, must_list1, may_list1))) else
	              let tmp1 = MCP.merge_mems (MCP.combine_mix_branch branch_id_added (xpure_lhs_h1, xpure_lhs_h1_b))
                    (MCP.combine_mix_branch branch_id_added (lhs_new, lhs_b)) false in
	              let new_ante, new_conseq = heap_entail_build_mix_formula_check
                    (estate.es_evars@estate.es_gen_expl_vars@estate.es_gen_impl_vars) tmp1 rhs_p pos in
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
		          let (r1, r2, r3) = (imply_mix_formula_no_memo new_ante new_conseq !imp_no !imp_subno None memset) in
                  (r1, r2, r3, (bug_kind, (contra_list1, must_list1, may_list1)))
              in
              List.fold_left fold_fun (false,[],None, (new_fc_kind, (new_contra_list, new_must_list, new_may_list))) branches
            end
          else (i_res1,i_res2,i_res3, (fc_kind, (contra_list, must_list, may_list)))
        in
	    (imp_no := !imp_no+1;
	    (res1, res2@succs,i_res3, (fn_fc_kind, (fn_contra_list, fn_must_list, fn_may_list))))
    end (* end of fold_fun_impt *)
  in
  
  let prf = mkPure estate (CP.mkTrue no_pos) (CP.mkTrue no_pos) true None in
  let memo_r_br = List.map (fun (c1,c2)-> (c1,MCP.memoise_add_pure_N (MCP.mkMTrue pos) c2)) rhs_p_br in
  let (r_rez,r_succ_match, r_fail_match, (fc_kind, (contra_list, must_list, may_list))) = 
    List.fold_left fold_fun_impt  (true,[],None, (Failure_Valid, ([],[],[])))  (("", rhs_p) :: memo_r_br) in
  (*let _ = print_string ("An Hoa :: memo_r_br =\n") in*)
  (*let _ = List.map (fun (c1,c2) -> print_string (c1 ^ Cprinter.string_of_mix_formula c2)) memo_r_br in*)   
  (* An Hoa note: THE FOLLOWING let DOES ALL THE WORK! *)
  (*let _ = print_string ("After folding :  " ^  (string_of_bool r_rez) ^ "\n") in*)
  if r_rez then begin (* Entailment is valid *)
    if not(stk_estate # is_empty) then
      let new_estate = stk_estate # top in
      let ctx1 = (elim_unsat_es_now prog (ref 1) new_estate) in
      let ctx1 = add_infer_pure_to_ctx (stk_inf_pure # get_stk) ctx1  in
      (SuccCtx[ctx1],UnsatAnte)
    else
      let inf_p = (stk_inf_pure # get_stk) in
      let estate = add_infer_pure_to_estate inf_p estate in
      let to_add = MCP.mix_of_pure (CP.join_conjunctions inf_p) in
	  let lhs_p = MCP.merge_mems lhs_new to_add true in
      let res_delta = mkBase lhs_h lhs_p lhs_t lhs_fl lhs_b no_pos in
      (*    let lhs_xpure,_,_,_ = xpure prog res_delta in                                                              *)
      (*    let rhs_xpure = rhs_p in                                                                                   *)
      (*    let r = Inf.infer_pure estate lhs_xpure rhs_xpure pos in                                                   *)
      (*    match r with                                                                                               *)
      (*      | Some (new_p, new_estate) ->                                                                            *)
      (*        let ctx1 = (Ctx new_estate) in                                                                         *)
      (*        let ctx1 = set_unsat_flag ctx1 true in                                                                 *)
      (*        let r1, prf = heap_entail_one_context prog is_folding ctx1 (CF.formula_of_mix_formula rhs_p pos) pos in*)
      (*        (r1,prf)                                                                                               *)
      (*      | None ->                                                                                                *)
	  if is_folding then begin
        (*LDK: the rhs_p is considered a part of residue and 
          is added to es_pure only when folding.
          Rule F-EMP in Mr Hai thesis, p86*)
	    let res_es = {estate with es_formula = res_delta; 
		    es_pure = ((MCP.merge_mems rhs_p (fst estate.es_pure) true),(Cpure.merge_branches (snd estate.es_pure) rhs_p_br));
		    es_success_pts = (List.fold_left (fun a (c1,c2)-> match (c1,c2) with
			  | Some s1,Some s2 -> (s1,s2)::a
			  | _ -> a) [] r_succ_match)@estate.es_success_pts;
		    es_unsat_flag = false;} in
	    let res_ctx = Ctx (CF.add_to_estate res_es "folding performed") in
	  Debug.devel_zprint (lazy ("heap_entail_empty_heap: folding: formula is valid")) pos;
	  Debug.devel_zprint (lazy ("heap_entail_empty_heap: folding: res_ctx:\n" ^ (Cprinter.string_of_context res_ctx))) pos;
	    (*let _ = print_string ("An Hoa :: heap_entail_empty_heap: folding: res_ctx:\n" ^ (Cprinter.string_of_context res_ctx) ^ "\n") in*)
	    (SuccCtx[res_ctx], prf)
	  end
	  else begin
	    let res_ctx = Ctx {estate with es_formula = res_delta;
            (*LDK: ??? add rhs_p into residue( EMP rule in p78). 
              Similar to the above
              Currently, we do not add the whole rhs_p into the residue.
              We only instatiate ivars and expl_vars in
              heap_entail_conjunct_helper *)
            (*TO CHECK: important to instantiate ivars*)
		    (* es_pure = ((MCP.merge_mems rhs_p (fst estate.es_pure) true),(Cpure.merge_branches (snd estate.es_pure) rhs_p_br)); (\*LDK*\) *)
		    es_success_pts = (List.fold_left (fun a (c1,c2)-> match (c1,c2) with
			  | Some s1,Some s2 -> (s1,s2)::a
			  | _ -> a) [] r_succ_match)@estate.es_success_pts;} in
	  Debug.devel_zprint (lazy ("heap_entail_empty_heap: formula is valid")) pos;
	  Debug.devel_zprint (lazy ("heap_entail_empty_heap: res_ctx:\n" ^ (Cprinter.string_of_context res_ctx))) pos;
   	    (*let _ = print_string ("An Hoa :: heap_entail_empty_heap :: res_ctx:\n" ^ (Cprinter.string_of_context res_ctx) ^ "\n") in*)
	    (SuccCtx[res_ctx], prf)
	  end
  end
  else
    (*** CODE TO INFER PRECOND ***)
    (* let lhs_xpure,_,_,_ = xpure prog estate.es_formula in *)
    (* let rhs_xpure = rhs_p in *)
    (* let r = Inf.infer_pure_m 1 estate lhs_xpure rhs_xpure pos in *)
    (* (\* let _ = Inf.infer_lhs_rhs_pure_es estate lhs_xpure rhs_xpure pos in *\) *)
    (* match r with *)
    (*   | Some (new_estate,pf) -> *)
    (*         (\* explicitly force unsat checking to be done here *\) *)
    (*         let ctx1 = (elim_unsat_es_now prog (ref 1) new_estate) in *)
    (*         (\* let _ = print_endline ("WN after elim_unsat 3:"^(Cprinter.string_of_context ctx1)) in *\) *)
    (*         (\* let ctx1 = (Ctx new_estate) in *\) *)
    (*         (\* let ctx1 = set_unsat_flag ctx1 true in  *\) *)
    (*         let r1, prf = heap_entail_one_context prog is_folding ctx1 (CF.formula_of_mix_formula rhs_p pos) pos in *)
    (*         let r1 = add_infer_pure_to_list_context [pf] r1 in *)
    (*         (r1,prf) *)
    (*   | None -> *)
    (*** CODE TO INFER PRECOND ***)
    begin
              Debug.devel_zprint (lazy ("heap_entail_empty_rhs_heap: formula is not valid\n")) pos;
      (*compute lub of estate.es_formula and current fc_flow*)
      (*
        fc_flow: safe -> normal_flow --or higher
        must bug -> sleek_mustbug_flow
        may bug -> sleek_maybug_flow
      *)
      if not !disable_failure_explaining then
        let new_estate = {
            estate with es_formula =
                match fc_kind with
                  | CF.Failure_Must _ -> CF.substitute_flow_into_f !error_flow_int estate.es_formula
                  | CF.Failure_May _ -> CF.substitute_flow_into_f !top_flow_int estate.es_formula
                        (* this denotes a maybe error *)
                  | CF.Failure_Bot _ -> estate.es_formula
                  | CF.Failure_Valid -> estate.es_formula
        } in
        let fc_template = {
		    fc_message = "??? 4785";
		    fc_current_lhs  = new_estate;
		    fc_prior_steps = estate.es_prior_steps;
		    fc_orig_conseq  = struc_formula_of_formula (formula_of_mix_formula_with_branches rhs_p rhs_p_br pos) pos;
		    fc_current_conseq = CF.formula_of_heap HFalse pos;
		    fc_failure_pts = match r_fail_match with | Some s -> [s]| None-> [];} in
        (build_and_failures 1 "213" Globals.logical_error (contra_list, must_list, may_list) fc_template, prf)
      else
        (CF.mkFailCtx_in (Basic_Reason ({
		    fc_message = "failed in entailing pure formula(s) in conseq";
		    fc_current_lhs  = estate;
		    fc_prior_steps = estate.es_prior_steps;
		    fc_orig_conseq  = struc_formula_of_formula (formula_of_mix_formula_with_branches rhs_p rhs_p_br pos) pos;
		    fc_current_conseq = CF.formula_of_heap HFalse pos;
		    fc_failure_pts = match r_fail_match with | Some s -> [s]| None-> [];},
        {fe_kind = fc_kind; fe_name = Globals.logical_error ;fe_locs=[]})), prf)
    end
        (****************************************************************)  
        (* utilities for splitting the disjunctions in the antecedent and the conjunctions in the consequent *)
        (****************************************************************)  
        (* 
	       try to solve the inequalities from the rhs by making queries to the memory set:
	       - if the inequality cannot be solved -> leave it in the conseq
	       - if the equality is solved -> remove it from conseq 
        *)

(* detect if there is a constradiction between the ptr equations generated by ante and the disjointness sets in memset *)
and detect_false (ante : MCP.mix_formula) (memset : CF.mem_formula) : bool =
  (* if not (TP.is_sat_mix_sub_no ante (ref 1) true true) then true
  else *)
  let eqset = match ante with
    | MCP.MemoF at ->
        MCP.ptr_equations_aux_mp false at 
    | MCP.OnePF at ->
        pure_ptr_equations at 
  in
	let eqset = CP.EMapSV.build_eset eqset in
	(* let neq_pairs = CF.generate_disj_pairs_from_memf memset in *)
	(* List.fold_left *)
	(*    (fun x y -> x || (CP.EMapSV.is_equiv eqset (fst y) (snd y))) false neq_pairs *)
	let m = memset.mem_formula_mset in
	let rec helper l =
	  match l with
	    | h::r -> 
	      if (r!=[]) then
		(List.fold_left 
		   (fun x y -> x || CP.EMapSV.is_equiv eqset h y) false r) || (helper r)
	      else false
	    | [] -> false
	in
	List.fold_left 
	  (fun x y -> x || (helper y)) false m

and solve_ineq a m c = 
  Debug.no_3 "solve_ineq "
      (Cprinter.string_of_mix_formula) 
      (Cprinter.string_of_mem_formula)
      (Cprinter.string_of_mix_formula) 
      (Cprinter.string_of_mix_formula) (fun _ _ _ -> solve_ineq_x a m c) a m c

and solve_ineq_x (ante_m0:MCP.mix_formula) (memset : Cformula.mem_formula) 
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
           {Error.error_loc = no_pos; Error.error_text = ("antecedent and consequent mismatch")}
           

and solve_ineq_pure_formula_debug (ante : Cpure.formula) (memset : Cformula.mem_formula) (conseq : Cpure.formula) : Cpure.formula =
  Debug.no_3 "solve_ineq_pure_formula "
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

and solve_ineq_memo_formula (ante : memo_pure) (memset : Cformula.mem_formula) (conseq : memo_pure) : memo_pure =
  let eqset = CP.EMapSV.build_eset (MCP.ptr_equations_aux_mp false ante) in
  let eq x y = CP.EMapSV.is_equiv eqset x y in
  let f_memo x = None in
  let f_aset x = None in
  let f_formula x = None in
  let f_b_formula e =
	let (pf,il) = e in
	match pf with
      | CP.Neq (e1,e2,_) -> 	if (CP.is_var e1) && (CP.is_var e2) then
	      let v1 = CP.to_var e1 in
	      let v2 = CP.to_var e2 in
	      let discharge = CP.DisjSetSV.is_disj eq memset.Cformula.mem_formula_mset v1 v2 in
	      let ans = (if discharge then (CP.BConst(true,no_pos),il) else e) in 
          Some ans 
        else None
      | _ -> None in
  let f_exp x = None in
  let f = (f_memo, f_aset, f_formula, f_b_formula, f_exp) in
  MCP.transform_memo_formula f conseq

(* check whether the disjunction is of the form (x<y | y<x) which can be discharged by using the memory set *)
and check_disj ante memset l (f1 : Cpure.formula) (f2 : Cpure.formula) pos : Cpure.formula = 
  let s_ineq = solve_ineq_pure_formula ante memset in
  match f1, f2 with 
    | CP.BForm((pf1, il1), label1), CP.BForm((pf2, il2), label2) -> 
	      (match pf1, pf2 with
	        | CP.Lt(e1, e2, _), CP.Lt(e3, e4, _) ->
	              (match e1, e2, e3, e4 with
		            | CP.Var(sv1, _), CP.Var(sv2, _), CP.Var(sv3, _), CP.Var(sv4, _) ->
		                  if (CP.eq_spec_var sv1 sv4) && (CP.eq_spec_var sv2 sv3)
		                  then 
			                s_ineq  (CP.BForm ((CP.Neq(CP.Var(sv1, pos), CP.Var(sv2, pos), pos), il1), label1))
		                  else
			                Cpure.Or((s_ineq f1), (s_ineq f2), l, pos)
		            | _, _, _, _ -> Cpure.Or((s_ineq f1), (s_ineq f2), l, pos)
	              )
	        | _, _ -> Cpure.Or((s_ineq f1), (s_ineq f2), l, pos)
	      )
    | _, _ -> Cpure.Or((s_ineq f1), (s_ineq f2), l, pos)

and solve_ineq_b_formula sem_eq memset conseq : Cpure.formula =
  let (pf,il) = conseq in
  match pf with
    | Cpure.Neq (e1, e2, pos) -> 
	      if (CP.is_var e1) && (CP.is_var e2) then
	        let eq = (fun x y -> sem_eq x y) in
	        let v1 = CP.to_var e1 in
	        let v2 = CP.to_var e2 in
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

(************************************* 
 methods for implication discharging
***************************************)

and imply_mix_formula_new ante_m0 ante_m1 conseq_m imp_no memset 
      :bool *(formula_label option * formula_label option) list * formula_label option =
  (* let _ = print_string ("\nSolver.ml: imply_mix_formula " ^ (string_of_int !imp_no)) in *)
  (* detect whether memset contradicts with any of the ptr equalities from antecedent *)
 let ante_m0 = if detect_false ante_m0 memset then MCP.mkMFalse no_pos else ante_m0 in
 let conseq_m = solve_ineq ante_m0 memset conseq_m in
  match ante_m0,ante_m1,conseq_m with
    | MCP.MemoF a, _, MCP.MemoF c -> MCP.imply_memo a c TP.imply imp_no
    | MCP.OnePF a0, MCP.OnePF a1 ,MCP.OnePF c -> 
          let increm_funct = 
            if !enable_incremental_proving then Some !TP.incremMethodsO
            else None in
          CP.imply_disj
              (CP.split_disjunctions a0) (* list with xpure0 antecedent disjunctions *)
              (CP.split_disjunctions a1) (* list with xpure1 antecedent disjunctions *)
              (CP.split_conjunctions c) (* list with consequent conjunctions *)
              TP.imply         (* imply method to be used for implication proving *)
              increm_funct
              imp_no
    | _ -> report_error no_pos ("imply_mix_formula: mix_formula mismatch")

and imply_mix_formula ante_m0 ante_m1 conseq_m imp_no memset =
  Debug.no_4 "imply_mix_formula" Cprinter.string_of_mix_formula
      Cprinter.string_of_mix_formula Cprinter.string_of_mix_formula 
      Cprinter.string_of_mem_formula
      (fun (r,_,_) -> string_of_bool r)
      (fun ante_m0 ante_m1 conseq_m memset -> imply_mix_formula_x ante_m0 ante_m1 conseq_m imp_no memset)
      ante_m0 ante_m1 conseq_m memset

and imply_mix_formula_x ante_m0 ante_m1 conseq_m imp_no memset 
      :bool *(formula_label option * formula_label option) list * formula_label option =
  (*let _ = print_string ("\nAn Hoa :: imply_mix_formula ::\n" ^*)
  (*"ANTECEDENT = " ^ (Cprinter.string_of_mix_formula ante_m0) ^ "\n" ^*)
  (*"CONSEQUENCE = " ^ (Cprinter.string_of_mix_formula conseq_m) ^ "\n\n") in*) 
  (* detect whether memset contradicts with any of the ptr equalities from antecedent *)
  let ante_m0 = if detect_false ante_m0 memset then MCP.mkMFalse no_pos else ante_m0 in
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
                (CP.split_disjunctions a0) 
                (CP.split_disjunctions a1) 
                (CP.split_conjunctions c) 
	            TP.imply 
	            imp_no
          end
    | _ -> report_error no_pos ("imply_mix_formula: mix_formula mismatch")

and imply_mix_formula_no_memo new_ante new_conseq imp_no imp_subno timeout memset =   
  Debug.no_3 "imply_mix_formula_no_memo" Cprinter.string_of_mix_formula Cprinter.string_of_mix_formula Cprinter.string_of_mem_formula
      (fun (r,_,_) -> string_of_bool r) 
      (fun new_ante new_conseq memset -> imply_mix_formula_no_memo_x new_ante new_conseq imp_no imp_subno timeout memset) 
      new_ante new_conseq memset 

and imply_mix_formula_no_memo_x new_ante new_conseq imp_no imp_subno timeout memset =   
  (* detect whether memset contradicts with any of the ptr equalities from antecedent *)
  let new_ante = if detect_false new_ante memset then MCP.mkMFalse no_pos else new_ante in
  let new_conseq = solve_ineq new_ante memset new_conseq in
  let (r1,r2,r3) =  
    match timeout with
      | None -> TP.mix_imply new_ante new_conseq ((string_of_int imp_no) ^ "." ^ (string_of_int imp_subno))
      | Some t -> TP.mix_imply_timeout new_ante new_conseq ((string_of_int imp_no) ^ "." ^ (string_of_int imp_subno)) t 
  in
  Debug.devel_zprint (lazy ("IMP #" ^ (string_of_int imp_no) ^ "." ^ (string_of_int imp_subno))) no_pos;
  (r1,r2,r3)

and imply_formula_no_memo new_ante new_conseq imp_no memset =   
  let new_conseq = solve_ineq_pure_formula new_ante memset new_conseq in
  let res,_,_ = TP.imply new_ante new_conseq ((string_of_int imp_no)) false None in
  Debug.devel_zprint (lazy ("IMP #" ^ (string_of_int imp_no))) no_pos;
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
        let (nctx,b) = sem_imply_add prog is_folding  fold_ctx bc1 !enable_syn_base_case in
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

and do_base_case_unfold_only prog ante conseq estate lhs_node rhs_node  is_folding pos rhs_b = 
  let pr x = match x with 
    | None -> "None"
    | Some _ -> "Some" in
  Debug.no_3 "do_base_case_unfold_only" 
      (* Cprinter.string_of_formula  *)
      (add_str "ante:" Cprinter.string_of_formula) 
      (add_str "LHS node" Cprinter.string_of_h_formula) 
      (add_str "RHS node" Cprinter.string_of_h_formula) 
      pr
      (fun _ _ _-> do_base_case_unfold_only_x prog ante conseq estate lhs_node rhs_node is_folding pos rhs_b) 
      ante lhs_node rhs_node 

and do_base_case_unfold_only_x prog ante conseq estate lhs_node rhs_node is_folding pos rhs_b =
  if (is_data lhs_node) then None
  else begin
    (Debug.devel_zprint (lazy ("do_base_case_unfold attempt for : " ^
	    (Cprinter.string_of_h_formula lhs_node))) pos);
    (* c1,v1,p1 *)
    let lhs_name,lhs_arg,lhs_var = get_node_name lhs_node, get_node_args lhs_node , get_node_var lhs_node in
    let _ = Gen.Profiling.push_time "empty_predicate_testing" in
    let lhs_vd = (look_up_view_def_raw prog.prog_view_decls lhs_name) in
    let fold_ctx = Ctx {(empty_es (mkTrueFlow ()) pos) with 
        es_formula = ante;
        es_heap = estate.es_heap;
        es_evars = estate.es_evars;
        es_gen_expl_vars = estate.es_gen_expl_vars; 
        es_gen_impl_vars = estate.es_gen_impl_vars; 
        es_ante_evars = estate.es_ante_evars;
        es_unsat_flag = false;
        es_prior_steps = estate.es_prior_steps;
        es_path_label = estate.es_path_label;
        es_var_measures = estate.es_var_measures;
        es_var_stack = estate.es_var_stack;
        es_orig_ante = estate.es_orig_ante;
        es_infer_vars = estate.es_infer_vars;
        es_infer_vars_dead = estate.es_infer_vars_dead;
        es_infer_vars_rel = estate.es_infer_vars_rel;
        es_infer_heap = estate.es_infer_heap;
        es_infer_pure = estate.es_infer_pure;
        es_infer_pure_thus = estate.es_infer_pure_thus;
        es_assumed_pure = estate.es_assumed_pure;
        es_infer_rel = estate.es_infer_rel;
    } in
    (* let vd = lhs_vd in *)
    (* let _ = print_string ("do_base_case_unfold_only_x:" *)
    (*                       ^ "\n ###  vd.view_name = " ^ (Cprinter.string_of_ident vd.view_name) *)
    (*                       ^ "\n ###  vd.view_base_case = " ^ (Cprinter.string_of_view_base_case  vd.view_base_case) *)
    (*                       ^ "\n ###  vd.view_raw_base_case = " ^ *)
    (*                           (match vd.view_raw_base_case with *)
    (*                             | None -> "" *)
    (*                             | Some f -> (Cprinter.string_of_formula f) *)
    (*                           ) *)
    (*                       ^ "\n\n") in *)
    let na,prf = match lhs_vd.view_base_case with
      | None ->  Debug.devel_zprint (lazy ("do_base_case_unfold attempt : unsuccessful for : " ^
	        (Cprinter.string_of_h_formula lhs_node))) pos;
            (CF.mkFailCtx_in(Basic_Reason ( {
			    fc_message ="failure 1 ?? when checking for aliased node";
			    fc_current_lhs = estate;
			    fc_prior_steps = estate.es_prior_steps;
			    fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
			    fc_current_conseq = conseq;
			    fc_failure_pts = match (get_node_label rhs_node) with | Some s-> [s] | _ -> [];},
            CF.mk_failure_must "9999" Globals.sl_error)), UnsatConseq)
      | Some (bc1,(base1,branches1)) -> 

            (* let _ = print_string ("do_base_case_unfold_only_x:"  *)
            (*                       ^ "\n ###  vd.view_name = " ^ (Cprinter.string_of_ident vd.view_name) *)
            (*                       ^ "\n ###  vd.view_base_case.bc1 = " ^ (Cprinter.string_of_pure_formula  bc1) *)
            (*                       ^ "\n ###  vd.view_base_case.base1 = " ^ (Cprinter.string_of_mix_formula  base1) *)
            (*                       ^ "\n ###  vd.view_raw_base_case = " ^  *)
            (*                           (match vd.view_raw_base_case with *)
            (*                             | None -> "" *)
            (*                             | Some f -> (Cprinter.string_of_formula f) *)
            (*                           ) *)
            (*                       ^ "\n\n") in *)

	        begin
              (*let _ = print_string ("ante: "^(Cprinter.string_of_formula ante)^"\n conseq "^(Cprinter.string_of_formula conseq)^"\n") in*)
              let fr_vars = (CP.SpecVar (Named lhs_vd.Cast.view_data_name, self, Unprimed)) :: lhs_vd.view_vars in			
              let to_vars = lhs_var :: lhs_arg in
              (*let _ = print_string ("from "^(Cprinter.string_of_spec_var_list fr_vars)^"\n to "^(Cprinter.string_of_spec_var_list to_vars)^"\n") in*)
              let base = MCP.subst_avoid_capture_memo fr_vars to_vars base1 in
              let branches = List.map (fun (c1,c2)-> (c1,Cpure.subst_avoid_capture fr_vars to_vars c2)) branches1 in
              let bc1 = Cpure.subst_avoid_capture fr_vars to_vars bc1 in
              let (nctx,b) = sem_imply_add prog is_folding  fold_ctx bc1 !enable_syn_base_case in
              if b then 
		        (*let _ = print_string ("successful base case guard proof \n ") in*)
                (* TODO : need to trigger UNSAT checking here *)
		        let ctx = unfold_context_unsat_now prog (prog, Some (base,branches, (lhs_name,lhs_arg))) (SuccCtx[nctx]) lhs_var pos in

		        Debug.devel_zprint (lazy ("do_base_case_unfold attempt : successful : " ^
 	                (Cprinter.string_of_h_formula lhs_node)^ 
                    "\n Start Ante :"^(Cprinter.string_of_formula ante)^
	                "\n New Ante :"^(Cprinter.string_of_list_context_short ctx))) pos; 
                (ctx,TrueConseq)
              else begin
                Debug.devel_zprint (lazy ("do_base_case_unfold attempt : unsuccessful for : " ^
	                (Cprinter.string_of_h_formula lhs_node))) pos; 
                (CF.mkFailCtx_in(Basic_Reason  ( { 
				    fc_message ="failure 2 ?? when checking for aliased node";
				    fc_current_lhs = estate;
				    fc_prior_steps = estate.es_prior_steps;
				    fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
				    fc_current_conseq = conseq;
				    fc_failure_pts = match (get_node_label rhs_node) with | Some s-> [s] | _ -> [];},
                CF.mk_failure_must "99" Globals.sl_error)),TrueConseq)
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

(*LDK*)
and do_lhs_case prog ante conseq estate lhs_node rhs_node is_folding pos =
  let pr x = match x with
    | None -> "None"
    | Some _ -> "Some" in
  Debug.no_4 "do_lhs_case"
      (add_str "ante" Cprinter.string_of_formula)
      (add_str "conseq" Cprinter.string_of_formula)
      (add_str "lhs node" Cprinter.string_of_h_formula)
      (add_str "rhs node" Cprinter.string_of_h_formula)
      pr
      (fun _ _ _ _-> do_lhs_case_x prog ante conseq estate lhs_node rhs_node is_folding pos)
      ante conseq lhs_node rhs_node

and do_lhs_case_x prog ante conseq estate lhs_node rhs_node is_folding pos=
  let c1,v1,p1 = get_node_name lhs_node, get_node_args lhs_node , get_node_var lhs_node in
  let vd = (look_up_view_def_raw prog.prog_view_decls c1) in
  let na,prf = 
    (match vd.view_base_case with
      | None ->
            Debug.devel_zprint (lazy ("do_lhs_case : unsuccessful for : "
            ^ (Cprinter.string_of_h_formula lhs_node))) pos;
            (CF.mkFailCtx_in(Basic_Reason ( {
			    fc_message ="failure 1 ?? no vd.view_base_case to do case analysis";
			    fc_current_lhs = estate;
			    fc_prior_steps = estate.es_prior_steps;
			    fc_orig_conseq = struc_formula_of_formula conseq pos; (* estate.es_orig_conseq; *)
			    fc_current_conseq = conseq;
			    fc_failure_pts = match (get_node_label rhs_node) with | Some s-> [s] | _ -> [];},
            CF.mk_failure_must "9999" Globals.sl_error)), UnsatConseq)
      |  Some (bc1,(base1,branches1)) ->
             (*Turn off lhs_case flag to disable further case analysis *)
             let new_ante = CF.set_lhs_case_of_a_view ante c1 false in

             let fr_vars = (CP.SpecVar (Named vd.Cast.view_data_name, self, Unprimed)) :: vd.view_vars in			
             let to_vars = p1 :: v1 in
             (* (\*let _ = print_string ("from "^(Cprinter.string_of_spec_var_list fr_vars)^"\n to "^(Cprinter.string_of_spec_var_list to_vars)^"\n") in*\) *)
             (* let base = MCP.subst_avoid_capture_memo fr_vars to_vars base1 in *)
             (* let branches = List.map (fun (c1,c2)-> (c1,Cpure.subst_avoid_capture fr_vars to_vars c2)) branches1 in *)
             let bc1 = Cpure.subst_avoid_capture fr_vars to_vars bc1 in
             let not_bc1 = Cpure.mkNot bc1 None no_pos in

             let fold_ctx = Ctx {(empty_es (mkTrueFlow ()) pos) with es_formula = ante;
                 es_heap = estate.es_heap;
                 es_evars = estate.es_evars;
                 es_gen_expl_vars = estate.es_gen_expl_vars; 
                 es_gen_impl_vars = estate.es_gen_impl_vars; 
                 es_ante_evars = estate.es_ante_evars;
                 es_unsat_flag = false;
                 es_prior_steps = estate.es_prior_steps;
                 es_path_label = estate.es_path_label;
                 es_orig_ante = estate.es_orig_ante;
                 es_infer_vars = estate.es_infer_vars;
                 es_infer_heap = estate.es_infer_heap;
                 es_infer_pure = estate.es_infer_pure;
                 es_infer_pure_thus = estate.es_infer_pure_thus;
                 es_assumed_pure = estate.es_assumed_pure;
                 es_infer_rel = estate.es_infer_rel;
                 (* WN Check : do we need to restore infer_heap/pure
                    here *)
                 es_var_measures = estate.es_var_measures;
                 es_var_stack = estate.es_var_stack;
		         } in
             (*to eliminate redundant case analysis, we check whether 
               current antecedent implies the base case condition that 
               we want to do case analysis
               if (ante |- bc) or (ante |- bc1) => don't need case analysis
             *)
             let (_,b1) = sem_imply_add prog is_folding  fold_ctx bc1 !enable_syn_base_case in
             let (_,b2) = sem_imply_add prog is_folding  fold_ctx not_bc1 !enable_syn_base_case in
             let new_ante1 = 
               if (b1 || b2) then 
                 (*no case analysis*)
                 new_ante
               else


                 (*Doing case analysis on LHS: ante & (base \/ not(base) ) *)
                 
                 (*this way not correct ??? *)
                 (* let case_formula = Cpure.mkOr bc1 not_bc1 None no_pos in *)
                 (* let new_ante1 = CF.normalize_combine new_ante (CF.formula_of_pure_formula case_formula no_pos) no_pos in *)

                 let or1 = CF.normalize_combine new_ante (CF.formula_of_pure_formula bc1 no_pos) no_pos in
                 let or2 = CF.normalize_combine new_ante (CF.formula_of_pure_formula not_bc1 no_pos) no_pos in
                 (CF.mkOr or1 or2 pos)
             in
             (* let _ = print_string ("do_lhs_case_x:"  *)
             (*                       ^ "\n ###  vd.view_name = " ^ (Cprinter.string_of_ident vd.view_name) *)
             (*                       ^ "\n ###  vd.view_base_case.bc1 = " ^ (Cprinter.string_of_pure_formula  bc1) *)
             (*                       ^ "\n ###  vd.view_base_case.base1 = " ^ (Cprinter.string_of_mix_formula  base1) *)
             (*                       ^ "\n ###  vd.view_raw_base_case = " ^  *)
             (*                           (match vd.view_raw_base_case with *)
             (*                             | None -> "" *)
             (*                             | Some f -> (Cprinter.string_of_formula f) *)
             (*                           ) *)
             (*                       ^ "\n\n") in *)

             (* let _ = print_string ("do_lhs_case_x:"  *)
             (*                        ^ "\n ### lhs_node = " ^ (Cprinter.string_of_h_formula lhs_node) *)
             (*                       ^ "\n ###  vd.view_base_case.bc1 = " ^ (Cprinter.string_of_pure_formula  bc1) *)
             (*                        ^ "\n ### b1 = " ^ (string_of_bool b1) *)
             (*                        ^ "\n ### b2 = " ^ (string_of_bool b2) *)
             (*                       ^ "\n ### ante = " ^ (Cprinter.string_of_formula ante) *)
             (*                       ^ "\n ### new_ante = " ^ (Cprinter.string_of_formula new_ante) *)
             (*                       ^ "\n ### new_ante1 = " ^ (Cprinter.string_of_formula new_ante1) *)
             (*                       ^ "\n\n" )in *)

             let ctx = build_context (Ctx estate) new_ante1 pos in
             let res_rs, prf1 = heap_entail_one_context prog is_folding ctx conseq pos in
             (res_rs, prf1)
    )
  in
  Some (na,prf)

and do_match prog estate l_node r_node rhs (rhs_matched_set:CP.spec_var list) is_folding pos : list_context *proof =
  let pr (e,_) = Cprinter.string_of_list_context e in
  let pr_h = Cprinter.string_of_h_formula in
  Debug.no_5 "do_match" pr_h pr_h Cprinter.string_of_estate Cprinter.string_of_formula
      Cprinter.string_of_spec_var_list pr
      (fun _ _ _ _ _ -> do_match_x prog estate l_node r_node rhs rhs_matched_set is_folding pos)
      l_node r_node estate rhs rhs_matched_set

and do_match_x prog estate l_node r_node rhs (rhs_matched_set:CP.spec_var list) is_folding pos : 
      list_context *proof =
  (* print_endline ("[do_match] input LHS = "^ (Cprinter.string_of_entail_state estate)); *)
  (* print_endline ("[do_match] RHS = "^ (Cprinter.string_of_formula rhs)); *)
  (* print_endline ("[do_match] matching " ^ (Cprinter.string_of_h_formula l_node) ^ " |- " ^ (Cprinter.string_of_h_formula r_node)); *)
  Debug.devel_zprint (lazy ("do_match: using " ^
	  (Cprinter.string_of_h_formula l_node)	^ " to prove " ^
	  (Cprinter.string_of_h_formula r_node))) pos;
    (* Debug.devel_zprint (lazy ("do_match: source LHS: "^ (Cprinter.string_of_entail_state estate))) pos; *)
    (* Debug.devel_zprint (lazy ("do_match: source RHS: "^ (Cprinter.string_of_formula rhs))) pos; *)
    let l_args, l_node_name, l_perm, l_ann = match l_node with
      | DataNode {h_formula_data_name = l_node_name;
        h_formula_data_perm = perm;
        h_formula_data_imm = ann;
        h_formula_data_arguments = l_args}
      | ViewNode {h_formula_view_name = l_node_name;
        h_formula_view_perm = perm;
        h_formula_view_imm = ann;
        h_formula_view_arguments = l_args} ->
            (l_args, l_node_name,perm,ann)
      | _ -> report_error no_pos "[solver.ml]: do_match non view input\n" in
    let r_args, r_node_name, r_var, r_perm, r_ann = match r_node with
      | DataNode {h_formula_data_name = r_node_name;
        h_formula_data_perm = perm;
        h_formula_data_imm = ann;
        h_formula_data_arguments = r_args;
        h_formula_data_node = r_var}
      | ViewNode {h_formula_view_name = r_node_name;
        h_formula_view_perm = perm;
        h_formula_view_imm = ann;
        h_formula_view_arguments = r_args;
        h_formula_view_node = r_var} ->
            (r_args, r_node_name, r_var,perm,ann)
      | _ -> report_error no_pos "[solver.ml]: do_match non view input\n" in     

	(* An Hoa : found out that the current design of do_match 
	   will eventually remove both nodes. Here, I detected that 
	   l_h & r_h captures the heap part. In order to capture 
	   the remaining part, we need to update l_h and r_h with 
	   the remaining of the l_node and r_node after matching 
	   (respectively. *)
    let es_impl_vars = estate.es_gen_impl_vars in
    let (r,ann_lhs,ann_rhs) = subtype_ann_gen es_impl_vars l_ann r_ann in
    if r==false 
    then 
      (CF.mkFailCtx_in (Basic_Reason (mkFailContext "Imm annotation mismatches" estate (CF.formula_of_heap HFalse pos) None pos, 
      CF.mk_failure_must "911 : mismatched annotation" Globals.sl_error)), NoAlias)
    else 
      (* let rhs = (match op_rhs with  *)
      (*   | None -> rhs *)
      (*   | Some bf -> Cformula.add_pure_formula_to_formula bf rhs) in *)
      let l_h,l_p,l_fl,l_b,l_t = split_components estate.es_formula in
      let r_h,r_p,r_fl,r_b,r_t = split_components rhs in
	  (* An Hoa : match l_node and r_node and push the remain to l_h, r_h *)
	  let rem_l_node,rem_r_node = match (l_node,r_node) with
	    | (DataNode dnl, DataNode dnr) -> (* let _ = print_endline ("[do_match] An Hoa Implementation : Push remains of data node matching to the lhs and rhs") in *)
			  let new_args = List.combine l_args r_args in
			  let hole = CP.SpecVar (UNK,"#",Unprimed) in
			  (* [Internal] function to cancel out two variables *)
			  let cancel_fun (x,y) = if (CP.is_hole_spec_var x || CP.is_hole_spec_var y) then 
			    (* 3 cases : (#,v) ; (#,#) ; (v,#) *) (x,y)
			  else (* (v,v) *) (hole,hole) in
 			  let new_args = List.map cancel_fun new_args in
			  let new_l_args,new_r_args = List.split new_args in
			  (* let _ = print_endline ("[do_match] cancelled lhs node = { " ^ (PR.string_of_spec_var_list new_l_args) ^ " } ==> " ^ (if CF.is_empty new_l_args then "empty" else "add to lhs")) in *)
			  (* let _ = print_endline ("[do_match] cancelled rhs node = { " ^ (PR.string_of_spec_var_list new_r_args) ^ " } ==> " ^ (if CF.is_empty new_r_args then "empty" else "add to rhs")) in *)
			  let new_l_holes = CF.compute_holes_list new_l_args in
			  let new_r_holes = CF.compute_holes_list new_r_args in
			  (* let _ = print_endline ("[do_match] lhs holes = { " ^ (String.concat "," (List.map string_of_int new_l_holes)) ^ " }") in *)
			  (* let _ = print_endline ("[do_match] rhs holes = { " ^ (String.concat "," (List.map string_of_int new_r_holes)) ^ " }") in *)
			  (* An Hoa : DO NOT ADD THE REMAINING TO THE LEFT HAND SIDE - IT MIGHT CAUSE INFINITE LOOP & CONTRADICTION AS THE l_h IS ALWAYS ADDED TO THE HEAP PART. *)
			  let rem_l_node = if (CF.is_empty new_l_args) then HTrue
			  else DataNode { dnl with
				  h_formula_data_arguments = new_l_args;
				  h_formula_data_holes = new_l_holes; } in
			  let rem_r_node = if (CF.is_empty new_r_args) then HTrue 
			  else DataNode { dnr with
				  h_formula_data_arguments = new_r_args;
				  h_formula_data_holes = new_r_holes;	} in
			  (* let new_r_h = match rem_r_node with
			     | HTrue -> r_h
			     | _ -> mkStarH r_h rem_r_node no_pos in *)
			  (rem_l_node,rem_r_node)
	    | _ -> (HFalse,HTrue) (* rem_l_node = HFalse only if the input are not data nodes. No change if we are not matching data node against data node *)
	  in
	  (* let _ = print_endline ("[do_match] remaining l_node and r_node = { " ^ PR.string_of_h_formula rem_l_node ^ " ; " ^ PR.string_of_h_formula rem_r_node ^ " }") in *)
	  match rem_r_node with (* Fail whenever the l_node cannot entail r_node *)
	    | DataNode _ -> (CF.mkFailCtx_in (Basic_Reason (mkFailContext "Cannot match LHS node and RHS node" estate (CF.formula_of_heap HFalse pos) None pos, 
          CF.mk_failure_must "99" Globals.sl_error)), NoAlias)
	    | _ -> 
	          (* An Hoa : end added code *)
              let label_list = try 
                let vdef = Cast.look_up_view_def_raw prog.prog_view_decls l_node_name in
                vdef.Cast.view_labels
              with Not_found -> List.map (fun _ -> "") l_args in
              (*LDK: using fractional permission introduces 1 more spec var
                We also need to add 1 more label*)
              let rho_0, label_list = 
                if (Perm.allow_perm ()) then
                  (match l_perm, r_perm with
                    | Some f1, Some f2 ->
                          let rho_0 = List.combine (f2::r_args) (f1::l_args) in
                          let label_list = (""::label_list) in
                          (rho_0, label_list)
                    | None, Some f2 ->
                          let rho_0 = List.combine (f2::r_args) (full_perm_var::l_args) in
                          let label_list = (""::label_list) in
                          (rho_0, label_list)
                    | Some f1, None ->
                          let rho_0 = List.combine (full_perm_var::r_args) (f1::l_args) in
                          let label_list = (""::label_list) in
                          (rho_0, label_list)
                    | _ -> let rho_0 = List.combine r_args l_args in
                      (rho_0, label_list)
                  )
                else  
                  let rho_0 = List.combine r_args l_args in (* without branch label *)
                  (rho_0, label_list)
              in
              let rho = List.combine rho_0 label_list in (* with branch label *)
              (*impl_tvars are impl_vars that are replaced by ivars in rho. 
                A pair (impl_var,ivar) belong to rho => 
                impl_var belongs to impl_tvars
                ivar belongs to ivars
                (ivar,impl_var) belongs to ivar_subs_to_conseq
              *)
              let ((impl_tvars, ivars, ivar_subs_to_conseq),other_subs) = subs_to_inst_vars rho estate.es_ivars es_impl_vars pos in
              let subtract = Gen.BList.difference_eq CP.eq_spec_var in
              let new_impl_vars = subtract es_impl_vars impl_tvars in
              let new_exist_vars = estate.es_evars(* @ivars *) in
              let new_expl_vars = estate.es_gen_expl_vars@impl_tvars in
              let new_ivars = subtract estate.es_ivars ivars in
              (* let (expl_inst, ivars', expl_vars') = (get_eqns_expl_inst rho_0 estate.es_ivars pos) in *)
              (* to_lhs only contains bindings for free vars that are not to be explicitly instantiated *)
              (*Only instantiate an RHS impl_var to LHS if 
                it is not matched with an ivar of LHS.
                if it is matched, it becomes expl_inst in new_expl_ins.
                Note: other_subs will never contain any impl_tvars because 
                of the pre-processed subs_to_inst_vars*)
	          (* An Hoa : strip all the pair of equality involving # *)
	          let other_subs = List.filter (fun ((x,y),_) -> not (CP.is_hole_spec_var x || CP.is_hole_spec_var y)) other_subs in
              let (to_lhs, to_lhs_br),(to_rhs,to_rhs_br),ext_subst = 
                get_eqns_free other_subs new_exist_vars impl_tvars (* estate.es_evars *) (* estate.es_expl_vars@ *) estate.es_gen_expl_vars pos in
              (* adding annotation constraints matched *)
              let to_rhs = (match ann_rhs with
                | None -> to_rhs
                | Some bf -> CP.mkAnd bf to_rhs no_pos) in
              let to_lhs = (match ann_lhs with
                | None -> to_lhs
                | Some bf -> CP.mkAnd bf to_lhs no_pos) in
              (*********************************************************************)
              (* handle both explicit and implicit instantiation *)
              (* for the universal vars from universal lemmas, we use the explicit instantiation mechanism,  while, for the rest of the cases, we use implicit instantiation *)
              (* explicit instantiation is like delaying the movement of the bindings for the free vars from the RHS to the LHS *)
              (********************************************************************)
              let new_ante_p = (MCP.memoise_add_pure_N l_p to_lhs ) in
              let new_conseq_p = (MCP.memoise_add_pure_N r_p to_rhs ) in
	          (* An Hoa : put the remain of l_node back to lhs if there is memory remaining after matching *)
	          let l_h = match rem_l_node with
		        | HTrue | HFalse -> l_h
		        | _ -> mkStarH rem_l_node l_h pos
	          in
	          (* let _ = print_endline ("[do_match] new lhs = " ^ PR.string_of_h_formula l_h) in *)
              let new_ante = mkBase l_h new_ante_p l_t l_fl (CP.merge_branches l_b to_lhs_br) pos in
	          (* An Hoa : fix new_ante *)
              let tmp_conseq = mkBase r_h new_conseq_p r_t r_fl (CP.merge_branches r_b to_rhs_br) pos  in

              let lhs_vars = ((CP.fv to_lhs) @(List.concat (List.map (fun (_,c)-> CP.fv c) to_lhs_br))) in
              (* apply the new bindings to the consequent *)
              let r_subs, l_sub = List.split (ivar_subs_to_conseq@ext_subst) in
              (*IMPORTANT TODO: global existential not took into consideration*)
              let tmp_conseq' = subst_avoid_capture r_subs l_sub tmp_conseq in

              let tmp_h2, tmp_p2, tmp_fl2, tmp_b2, _ = split_components tmp_conseq' in
              let new_conseq = mkBase tmp_h2 tmp_p2 r_t r_fl tmp_b2 pos in
	          (* An Hoa : TODO fix the consumption here - THIS CAUSES THE CONTRADICTION ON LEFT HAND SIDE! *)
              (* only add the consumed node if the node matched on the rhs is mutable *)
              let new_consumed = 
                if not(isLend (get_imm r_node))
                then (*let _ = print_string("add to history " ^ (Cprinter.string_of_h_formula r_node) ^ "\n") in*) mkStarH l_node estate.es_heap pos 
                else (* An Hoa : put l_node to the consumed heap portion if the matching leaves no remainder of l_node *)
		          (*match rem_l_node with 
		            | HTrue -> let _ = print_string("add to history " ^ (Cprinter.string_of_h_formula r_node) ^ "\n") in mkStarH l_node estate.es_heap pos 
		            | _ ->*) estate.es_heap
              in
	          (* let _ = print_endline ("[do_match] new consumed heap = " ^ PR.string_of_h_formula new_consumed) in *)
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
	          (* An Hoa : trace detected: need to change the left hand side before this point which forces to change the new_ante at an earlier check point *)
	          (* let _ = print_endline ("[do_match] New LHS = "^ (Cprinter.string_of_entail_state estate)) in *)
              (* let new_subst = (obtain_subst expl_inst) in *)
              (* apply the explicit instantiations to the consequent *)
              (* let new_conseq = subst_avoid_capture (fst new_subst) (snd new_subst) new_conseq in *)
              (* for each expl inst  vi = wi: make wi existential + remove vi from the exist vars *)
              let new_es' = new_es in (* {new_es with (\* es_evars = new_es.es_evars @ (snd new_subst); *\) es_must_match = false} in *)
              let new_es = pop_exists_estate ivars (* (fst new_subst) *) new_es' in
              let new_ctx = Ctx (CF.add_to_estate new_es "matching of view/node") in
	          (* print_endline ("[do_match] output LHS = " ^ (Cprinter.string_of_context_short new_ctx)); *)
	          (* print_endline ("[do_match] output RHS = " ^ (Cprinter.string_of_formula new_conseq)); *)
              Debug.devel_zprint (lazy ("do_match (after): LHS: "^ (Cprinter.string_of_context_short new_ctx))) pos;
              Debug.devel_zprint (lazy ("do_match (after): RHS:"
	          ^ (Cprinter.string_of_formula new_conseq))) pos;
              let res_es1, prf1 = (*heap_entail_split_rhs_phases*) heap_entail_conjunct prog is_folding  new_ctx new_conseq
                (rhs_matched_set @ [r_var]) pos in
              (Cformula.add_to_subst res_es1 r_subs l_sub, prf1)

and heap_entail_non_empty_rhs_heap_x prog is_folding  ctx0 estate ante conseq lhs_b rhs_b (rhs_h_matched_set:CP.spec_var list) pos : (list_context * proof) =
  Debug.devel_zprint (lazy ("heap_entail_conjunct_non_empty_rhs_heap:"
  ^ "\ncontext:\n" ^ (Cprinter.string_of_context ctx0)
  ^ "\nconseq:\n" ^ (Cprinter.string_of_formula conseq))) pos;
    let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_br) = CF.extr_formula_base lhs_b in
    let (rhs_h,rhs_p,rhs_t,rhs_fl,rhs_br) = CF.extr_formula_base rhs_b in
    let rhs_lst = split_linear_node_guided ( CP.remove_dups_svl (h_fv lhs_h @ MCP.mfv lhs_p)) rhs_h in
    let posib_r_alias = (estate.es_evars @ estate.es_gen_impl_vars @ estate.es_gen_expl_vars) in
    let rhs_eqset = estate.es_rhs_eqset in
    (* let _ = print_endline "CA:1" in *)
    let actions = Context.compute_actions prog rhs_eqset lhs_h lhs_p rhs_p posib_r_alias rhs_lst estate.es_is_normalizing pos in
    process_action 1 prog estate conseq lhs_b rhs_b actions rhs_h_matched_set is_folding pos

and heap_entail_non_empty_rhs_heap prog is_folding  ctx0 estate ante conseq lhs_b rhs_b (rhs_h_matched_set:CP.spec_var list) pos : (list_context * proof) =
  (*LDK*)
  Debug.no_3 "heap_entail_non_empty_rhs_heap" 
      Cprinter.string_of_formula_base 
      Cprinter.string_of_formula
      Cprinter.string_of_spec_var_list 
      (pr_pair Cprinter.string_of_list_context string_of_proof) 
      (fun _ _ _-> heap_entail_non_empty_rhs_heap_x prog is_folding  ctx0 estate ante conseq lhs_b rhs_b rhs_h_matched_set pos) lhs_b conseq rhs_h_matched_set

(* Debug.loop_3_no "heap_entail_non_empty_rhs_heap" Cprinter.string_of_formula_base Cprinter.string_of_formula *)
(*     Cprinter.string_of_spec_var_list (fun _ -> "?") (fun _ _ _-> heap_entail_non_empty_rhs_heap_x prog is_folding  ctx0 estate ante conseq lhs_b rhs_b rhs_h_matched_set pos) lhs_b conseq rhs_h_matched_set *)

and existential_eliminator_helper prog estate (var_to_fold:Cpure.spec_var) (c2:ident) (v2:Cpure.spec_var list) rhs_p = 
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr p = pr_pair pr_svl (pr_option Cprinter.string_of_pure_formula) p in
  let pr_rhs = Cprinter.string_of_mix_formula in
  let pr_es = Cprinter.string_of_entail_state in
  (*let t (r,_) = not(Gen.BList.list_equiv_eq CP.eq_spec_var (var_to_fold::v2) r) in*)
  Debug.no_5(*_opt t*) "existential_eliminator_helper" 
      pr_es 
      (add_str "Var2Fold:" Cprinter.string_of_spec_var) 
      (add_str "Pred:" pr_id) 
      (add_str "SVL:" Cprinter.string_of_spec_var_list) 
      (add_str "RHS pure:" pr_rhs) 
      pr 
      (fun _ _ _ _ _ -> existential_eliminator_helper_x prog estate (var_to_fold:Cpure.spec_var) (c2:ident) (v2:Cpure.spec_var list) rhs_p) 
      estate var_to_fold c2 v2 rhs_p 

(* this helper does not seem to eliminate anything *)
and existential_eliminator_helper_x prog estate (var_to_fold:Cpure.spec_var) (c2:ident) (v2:Cpure.spec_var list) rhs_p = 
  let comparator v1 v2 = (String.compare (Cpure.name_of_spec_var v1) (Cpure.name_of_spec_var v2))==0 in
  let pure = 
    (* if !allow_imm && (estate.es_imm_pure_stk!=[])  *)
    (* then MCP.pure_of_mix (List.hd estate.es_imm_pure_stk)  *)
    (* else *) MCP.pure_of_mix rhs_p in
  let ptr_eq = MCP.ptr_equations_with_null rhs_p in

  (* below are equality in RHS taken away during --imm option *)
  (* let _ = print_line "Adding es_rhs_eqset into RHS ptrs" in *)
  let ptr_eq = (* Cprinter.app_sv_print *) ptr_eq@(estate.es_rhs_eqset) in 
  let ptr_eq = (List.map (fun c->(c,c)) v2) @ ptr_eq in
  let asets = Context.alias_nth 9 ptr_eq in
  try
	let vdef = look_up_view_def_raw prog.Cast.prog_view_decls c2 in
	let subs_vars = List.combine vdef.view_vars v2 in
	let sf = (CP.SpecVar (Named vdef.Cast.view_data_name, self, Unprimed)) in
	let subs_vars = (sf,var_to_fold)::subs_vars in
    let vars_of_int = List.fold_left (fun a (c1,c2)-> if (List.exists (comparator c1) vdef.view_case_vars) then  c2::a else a) [] subs_vars in
    let vars_of_int = Gen.BList.intersect_eq comparator estate.es_gen_expl_vars vars_of_int in
    let posib_inst = CP.compute_instantiations pure vars_of_int (CF.fv estate.es_formula) in
	let l_args,pr = List.fold_left (fun (a,p) (c1,c2)->
		if (List.exists (comparator c1) vdef.view_case_vars) then
          let ex_vars = estate.es_evars@estate.es_gen_impl_vars@estate.es_gen_expl_vars in
		  if (List.exists (comparator c2) ex_vars) then
			try
              let c21 = List.find (fun c -> not (List.exists (comparator c) (ex_vars) )) (Context.get_aset asets c2) in
              (c21::a,p)
            with
              | Not_found ->
                    let _,np = List.find (fun (v,_)-> comparator v c2) posib_inst in
                    (c2::a,CP.mkAnd p np no_pos)
		  else (c2::a,p)
		else (c2::a,p)
	) ([],Cpure.mkTrue no_pos) subs_vars in
    (List.rev l_args, Some pr)
  with | Not_found -> (var_to_fold::v2,None) 

and inst_before_fold estate rhs_p view_vars = 
  let pr_sv = Cprinter.string_of_spec_var in
  let pr_1 = Cprinter.string_of_entail_state in
  let pr_2 = Cprinter.string_of_mix_formula in
  let pr_3 = Gen.Basic.pr_list pr_sv in
  let pr_r = Gen.Basic.pr_triple pr_1 pr_2 (Gen.Basic.pr_list (Gen.Basic.pr_pair pr_sv pr_sv)) in
  Debug.no_3 "inst_before_fold"  pr_1 pr_2 pr_3 pr_r
      (fun _ _ _ -> inst_before_fold_x estate rhs_p view_vars) estate rhs_p view_vars
      
and inst_before_fold_x estate rhs_p case_vars = 
  let lhs_fv = fv estate.es_formula in
  let of_interest = (*case_vars*) estate.es_gen_impl_vars in
  
  let rec filter b = match (fst b) with 
    | CP.Eq (lhs_e, rhs_e, _) ->
          let lfv = CP.afv lhs_e in
		  let rfv = CP.afv rhs_e in
		  let l_inter = Gen.BList.intersect_eq CP.eq_spec_var lfv of_interest in
		  let r_inter = Gen.BList.intersect_eq CP.eq_spec_var rfv of_interest in
		  let v_l = l_inter@r_inter in
		  let cond = 				
			let rec prop_e e = match e with 
			  | CP.Null _ | CP.Var _ | CP.IConst _ | CP.FConst _ | CP.AConst _ -> true
			  | CP.Subtract (e1,e2,_) | CP.Mult (e1,e2,_) | CP.Div (e1,e2,_) | CP.Add (e1,e2,_) -> prop_e e1 && prop_e e2
			  | CP.Bag (l,_) | CP.BagUnion (l,_) | CP.BagIntersect (l,_) -> List.for_all prop_e l
			  | CP.Max _ | CP.Min _ | CP.BagDiff _ | CP.List _ | CP.ListCons _ | CP.ListHead _ 
			  | CP.ListTail _ | CP.ListLength _ | CP.ListAppend _	| CP.ListReverse _ | CP.ArrayAt _ | CP.Func _ -> false in
			((List.length v_l)=1) && (Gen.BList.disjoint_eq CP.eq_spec_var lfv rfv)&& 
				((Gen.BList.list_subset_eq CP.eq_spec_var lfv lhs_fv && List.length r_inter == 1 && Gen.BList.list_subset_eq CP.eq_spec_var rfv (r_inter@lhs_fv) && prop_e rhs_e)||
				    (Gen.BList.list_subset_eq CP.eq_spec_var rfv lhs_fv && List.length l_inter == 1 && Gen.BList.list_subset_eq CP.eq_spec_var lfv (l_inter@lhs_fv)&& prop_e lhs_e)) in
		  if cond then (false,[(b,List.hd v_l)]) (*the bool states if the constraint needs to be moved or not from the RHS*)
          else (true,[])
    | _ -> (true,[])in
  let new_c,to_a = MCP.constraint_collector filter rhs_p in 
  let to_a_e,to_a_i = List.partition (fun (_,v)-> List.exists (CP.eq_spec_var v) estate.es_evars ) to_a in
  let to_a_e,rho = List.split (List.map (fun (f,v) -> 
      let v1 = CP.fresh_spec_var v in
      (CP.b_subst [(v,v1)] f, (v,v1))) to_a_e) in
  let to_a = (fst (List.split to_a_i))@to_a_e in
  let to_a = MCP.mix_of_pure (CP.conj_of_list (List.map (fun f-> CP.BForm (f,None)) to_a) no_pos) in
  let mv_fv = MCP.mfv to_a in
  let estate1 = {estate with es_formula = 
		  normalize_combine estate.es_formula (formula_of_mix_formula to_a no_pos) no_pos;
	  (*es_pure = ((MCP.memoise_add_pure_N (fst estate.es_pure) to_a), snd estate.es_pure);*) 							 
	  (*es_gen_expl_vars = Gen.BList.difference_eq CP.eq_spec_var estate.es_gen_expl_vars mv_fv; *)
	  es_evars = Gen.BList.difference_eq CP.eq_spec_var estate.es_evars mv_fv;
	  es_gen_impl_vars = Gen.BList.difference_eq CP.eq_spec_var estate.es_gen_impl_vars mv_fv;} in
  (estate1,new_c, rho)

      
and do_fold_w_ctx fold_ctx prog estate conseq rhs_node vd rhs_rest rhs_b is_folding pos = 
  let pr2 x = match x with
    | None -> "None"
    | Some (iv,f) -> Cprinter.string_of_struc_formula f.view_formula in
  let pr (x,_) = Cprinter.string_of_list_context_short x in
  let pr1 (conseq, rhs_node, vd ,rhs_rest,rhs_b) =
    ("\n conseq = "^(Cprinter.string_of_formula conseq)
    ^ "\n rhs_node = "^(Cprinter.string_of_h_formula rhs_node)
    ^ "\n vd = "^(pr2 vd)
    ^ "\n rhs_rest = "^(Cprinter.string_of_h_formula rhs_rest)
    ^ "\n rhs_b = "^(Cprinter.string_of_formula_base rhs_b)
    ^ "") in
  Debug.no_3(* _no *)  "do_fold_w_ctx" 
      Cprinter.string_of_context
      (* Cprinter.string_of_entail_state *)
      pr1
      string_of_bool
      pr
      (fun _ _ _ -> do_fold_w_ctx_x fold_ctx prog estate conseq rhs_node vd rhs_rest rhs_b is_folding pos) 
      fold_ctx (* estate *) (conseq, rhs_node, vd ,rhs_rest,rhs_b) is_folding

(* Debug.loop_3(\* _no *\)  "do_fold_w_ctx" Cprinter.string_of_context Cprinter.string_of_h_formula pr2 pr *)
(*     (fun _ _ _ -> do_fold_w_ctx_x fold_ctx prog estate conseq rhs_node vd rhs_rest rhs_b is_folding pos)  *)
(*     fold_ctx rhs_node vd *)
(*
  ln2 = p2 (node) c2 (name) v2 (arguments) r_rem_brs (remaining branches) r_p_cond (pruning conditions) pos2 (pos)
  resth2 = rhs_h - ln2
  ctx0?
  is_folding?
*)

(*LDK:
  ln2: node to fold

*)
and do_fold_w_ctx_x fold_ctx prog estate conseq ln2 vd resth2 rhs_b is_folding pos =
  let (ivars,vd) = match vd with 
    | None -> ([],None)
    | Some (iv,f) -> (iv, Some f) in
  let var_to_fold = get_node_var ln2 in
  let ctx0 = Ctx estate in
  let (rhs_h,rhs_p,rhs_t,rhs_fl,rhs_br) = CF.extr_formula_base rhs_b in
  let (p2,c2,perm,v2,pid,r_rem_brs,r_p_cond,pos2) = 
    match ln2 with
      | DataNode ({ h_formula_data_node = p2;
        h_formula_data_name = c2;
        h_formula_data_imm = imm2;
        h_formula_data_perm = perm;
        h_formula_data_arguments = v2;
        h_formula_data_label = pid;
        h_formula_data_remaining_branches =r_rem_brs;
        h_formula_data_pruning_conditions = r_p_cond;
        h_formula_data_pos = pos2})
      | ViewNode ({ h_formula_view_node = p2;
        h_formula_view_name = c2;
        h_formula_view_imm = imm2;
        h_formula_view_perm = perm; (*LDK*)
        h_formula_view_arguments = v2;
        h_formula_view_label = pid;
        h_formula_view_remaining_branches = r_rem_brs;
        h_formula_view_pruning_conditions = r_p_cond;
        h_formula_view_pos = pos2}) -> (p2,c2,perm,v2,pid,r_rem_brs,r_p_cond,pos2)
      | _ -> report_error no_pos ("do_fold_w_ctx: data/view expected but instead ln2 is "^(Cprinter.string_of_h_formula ln2) ) in
  (* let _ = print_string("in do_fold\n") in *)
  let original2 = if (is_view ln2) then (get_view_original ln2) else true in
  let unfold_num = (get_view_unfold_num ln2) in
  let estate = estate_of_context fold_ctx pos2 in
  (*TO CHECK: what for ??? instantiate before folding*)
  (*  let estate,rhs_p,rho = inst_before_fold estate rhs_p [] in*)
  let (new_v2,case_inst) = existential_eliminator_helper prog estate (var_to_fold:Cpure.spec_var) (c2:ident) (v2:Cpure.spec_var list) rhs_p in
  let view_to_fold = ViewNode ({  
	  h_formula_view_node = List.hd new_v2 (*var_to_fold*);
	  h_formula_view_name = c2;
	  h_formula_view_derv = get_view_derv ln2;
	  h_formula_view_imm = get_view_imm ln2;
      h_formula_view_original = original2;
      h_formula_view_unfold_num = unfold_num;
      h_formula_view_perm = perm; (*LDK*)
      h_formula_view_arguments = List.tl new_v2;
      h_formula_view_modes = get_view_modes ln2;
      h_formula_view_coercible = true;
	  h_formula_view_lhs_case = false;
	  h_formula_view_origins = get_view_origins ln2;
	  h_formula_view_label = pid;           (*TODO: the other alternative is to use none*)
	  h_formula_view_remaining_branches = r_rem_brs;
	  h_formula_view_pruning_conditions = r_p_cond;
	  h_formula_view_pos = pos2}) in
  (*instantiation before the fold operation,
    for existential vars:
    rho = [b->b1]
    forall b1. D[a] & b1=a+1
    |- \rho x::lseg<b,..> & P & b=a+1
    ----------------------------------------------------
    D[a] |- ex b: x::lseg<b,..> & P & b=a+1
    for implicits: 
    D[a] & b=a+1 |- x::lseg<b,..> & P
    ---------------------------------------
    D[a] |- exI b: x::lseg<b,..> & P & b=a+1  
    
    inst_before_fold returns the new entail state with the instantiation already moved
    the remaining rhs pure, and a set of substitutions to be applied to the view node and the remaining conseq
    posib_inst is the list of view args that are case vars
  *)
  (*let view_to_fold = CF.h_subst rho view_to_fold in*)
  (*add rhs_p in case we need to propagate some pure constraints into folded view*)
  let fold_rs, fold_prf = fold_op prog (Ctx estate) view_to_fold vd rhs_p (* false *) case_inst pos in
  if not (CF.isFailCtx fold_rs) then
    let b = { formula_base_heap = resth2;
    formula_base_pure = rhs_p;
    formula_base_type = rhs_t;
    formula_base_branches = rhs_br;
    formula_base_flow = rhs_fl;		
    formula_base_label = None;   
    formula_base_pos = pos } in

    let perms = 
      if (Perm.allow_perm ()) then
        get_cperm perm
      else []
    in
    (*add permission vars if applicable*)
    let tmp, tmp_prf = process_fold_result ivars prog is_folding estate fold_rs p2 (perms@v2) b pos in
	let prf = mkFold ctx0 conseq p2 fold_prf tmp_prf in
	(tmp, prf)
  else begin
  unable_to_fold_rhs_heap := true;
	Debug.devel_zprint (lazy ("heap_entail_non_empty_rhs_heap: unable to fold:\n"
	^ (Cprinter.string_of_context ctx0) ^ "\n"
	^ "to:ln2: "
	^ (Cprinter.string_of_h_formula ln2)
	^ "\nrhs_p: "
	^ (Cprinter.string_of_mix_formula rhs_p) ^"..end")) pos;
	(fold_rs, fold_prf)
  end 

and combine_results_x ((res_es1,prf1): list_context * Prooftracer.proof) 
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
      
and combine_results ((res_es1,prf1): list_context * Prooftracer.proof) 
      ((res_es2,prf2): list_context * Prooftracer.proof) : list_context * Prooftracer.proof =
  let length_ctx ctx = match ctx with
    | CF.FailCtx _ -> 0
    | CF.SuccCtx ctx0 -> List.length ctx0 in
  let pr x = "\nctx length:" ^ (string_of_int (length_ctx (fst x))) ^ " \n Context:"^ Cprinter.string_of_list_context_short (fst x) (* ^ "\n Proof: " ^ (Prooftracer.string_of_proof (snd x)) *) in
  (*let pr3 = Cprinter.string_of_spec_var_list in*)
  Debug.no_2 "combine_results" pr pr pr (fun _ _ -> combine_results_x (res_es1,prf1) (res_es2,prf2)) (res_es1,prf1) (res_es2,prf2)

(* and do_fold_old prog vd estate conseq rhs_node rhs_rest rhs_b is_folding pos = *)
(*   (\* TODO : should we use estate as the base to perform modifications, *)
(*      instead of starting from empty_es! *\) *)
(*   let fold_ctx = Ctx {(empty_es (mkTrueFlow () ) pos) with  *)
(* 	  es_formula = estate.es_formula; *)
(* 	  es_heap = estate.es_heap; *)
(* 	  es_evars = estate.es_evars; *)
(* 	  es_gen_expl_vars = estate.es_gen_expl_vars;  *)
(* 	  es_gen_impl_vars = estate.es_gen_impl_vars;  *)
(* 	  es_ante_evars = estate.es_ante_evars; *)
(* 	  es_pure = estate.es_pure; *)
(* 	  es_unsat_flag  = false; *)
(* 	  es_success_pts = estate.es_success_pts; *)
(* 	  es_residue_pts = estate.es_residue_pts; *)
(* 	  es_id  = estate.es_id; *)
(* 	  es_rhs_eqset  = estate.es_rhs_eqset; (\* needed by --imm *\) *)
(* 	  es_orig_ante  = estate.es_orig_ante; *)
(* 	  es_orig_conseq = estate.es_orig_conseq; *)
(* 	  es_prior_steps = estate.es_prior_steps; *)
(*       es_path_label = estate.es_path_label; *)
(*       es_infer_vars = estate.es_infer_vars; *)
(*       es_infer_heap = estate.es_infer_heap; *)
(*       es_infer_pure = estate.es_infer_pure; *)
(* 	  es_var_measures = estate.es_var_measures; *)
(* 	  es_var_label = estate.es_var_label; *)
(* 	  es_var_ctx_lhs = estate.es_var_ctx_lhs; *)
(* 	  es_var_ctx_rhs = estate.es_var_ctx_rhs; *)
(* 	  es_var_subst = estate.es_var_subst; *)
(* 	  es_trace = estate.es_trace} in *)
(*   do_fold_w_ctx fold_ctx prog estate conseq rhs_node vd rhs_rest rhs_b is_folding pos *)
      
and do_fold prog vd estate conseq rhs_node rhs_rest rhs_b is_folding pos =
  let fold_ctx = Ctx { estate with
      (* without unsat_flag reset:
         error at: imm/kara-tight.ss karatsuba_mult
      *)
	    es_unsat_flag  = false;
	    es_ivars  = [];
      es_pp_subst = [];
      es_arith_subst = [];
      es_cont = [];
      es_crt_holes = [];
      es_hole_stk = [];                     
      es_aux_xpure_1 = MCP.mkMTrue pos;
      es_subst = ([], []);
      es_aux_conseq = CP.mkTrue pos;
      es_must_error = None;
  } in
  do_fold_w_ctx fold_ctx prog estate conseq rhs_node vd rhs_rest rhs_b is_folding pos

and do_base_fold_x prog estate conseq rhs_node rhs_rest rhs_b is_folding pos=
  let (estate,iv) = Inf.remove_infer_vars_all estate (* rt *)in
  let vd = (vdef_fold_use_bc prog rhs_node) in
  let (cl,prf) = 
    match vd with
        (* CF.mk_failure_must "99" Globals.sl_error)), NoAlias) *)
      | None ->
            (CF.mkFailCtx_in (Basic_Reason (mkFailContext "No base-case for folding" estate (CF.formula_of_heap HFalse pos) None pos, 
            CF.mk_failure_must "99" Globals.sl_error)), NoAlias)
      | Some vd ->
            do_fold prog (Some (iv,vd)) estate conseq rhs_node rhs_rest rhs_b is_folding pos 
  in  ((* Inf.restore_infer_vars iv  *)cl,prf)


and do_base_fold prog estate conseq rhs_node rhs_rest rhs_b is_folding pos=
  let pr2 x = Cprinter.string_of_list_context_short (fst x) in
  Debug.no_2 "do_base_fold" 
      Cprinter.string_of_entail_state Cprinter.string_of_formula pr2
      (fun _ _ -> do_base_fold_x prog estate conseq rhs_node rhs_rest rhs_b is_folding pos) estate conseq

and do_full_fold_x prog estate conseq rhs_node rhs_rest rhs_b is_folding pos = 
  do_fold prog None estate conseq rhs_node rhs_rest rhs_b is_folding pos

and do_full_fold prog estate conseq rhs_node rhs_rest rhs_b is_folding pos =
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 x = Cprinter.string_of_list_context_short (fst x) in
  Debug.no_2 "do_full_fold" Cprinter.string_of_entail_state pr1 pr2 
      (fun _ _ -> do_full_fold_x prog estate conseq rhs_node rhs_rest rhs_b is_folding pos) estate rhs_node
      

and push_hole_action_x a1 r1=
  match Context.action_get_holes a1 with
    | None -> r1
    | Some h -> push_crt_holes_list_ctx r1 h
and push_hole_action a1 r1=
  Debug.no_1_loop "push_hole_action" pr_no pr_no 
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
  Debug.no_2 "advance_unfold" pr1 p0 pr2 (fun _ _ -> advance_unfold_x prog ctx conseq) ctx conseq 

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
  Debug.no_2 "comp_act" pr1 pr2 pr3 (fun _ _ -> comp_act_x prog estate rhs) estate rhs

and comp_act_x prog (estate:entail_state) (rhs:formula) : (Context.action_wt) =
  let rhs_b = extr_rhs_b rhs in
  let lhs_b = extr_lhs_b estate in
  let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_br) = extr_formula_base lhs_b in
  let (rhs_h,rhs_p,rhs_t,rhs_fl,rhs_br) = extr_formula_base rhs_b in
  let rhs_lst = split_linear_node_guided ( CP.remove_dups_svl (h_fv lhs_h @ MCP.mfv lhs_p)) rhs_h in
  (* let rhs_lst = [] in *)
  let posib_r_alias = (estate.es_evars @ estate.es_gen_impl_vars @ estate.es_gen_expl_vars) in
  let rhs_eqset = estate.es_rhs_eqset in
  (* let _ = print_endline "CA:2" in *)
  (0,Context.compute_actions_x prog rhs_eqset lhs_h lhs_p rhs_p posib_r_alias rhs_lst  estate.es_is_normalizing no_pos)

and process_unfold_x prog estate conseq a is_folding pos has_post pid =
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

and do_infer_heap rhs rhs_rest caller prog estate conseq lhs_b rhs_b a (rhs_h_matched_set:CP.spec_var list) is_folding pos = 
  if Inf.no_infer estate then
    (CF.mkFailCtx_in (Basic_Reason (mkFailContext "infer_heap_node" estate (Base rhs_b) None pos,
    CF.mk_failure_must ("Disabled Infer heap and pure 2") sl_error)), NoAlias) 
  else
    (* TODO : this part is repeated in no_rhs_match; should optimize *)
    let lhs_xpure,_,_,_ = xpure prog estate.es_formula in
    let rhs_xpure,_,_,_ = xpure prog (formula_of_heap rhs no_pos) in
    let lhs_xpure = MCP.pure_of_mix lhs_xpure in
    let rhs_xpure = MCP.pure_of_mix rhs_xpure in
    let fml = CP.mkAnd lhs_xpure rhs_xpure pos in
    let check_sat = TP.is_sat_raw fml in
    (* check if there is a contraction with the RHS heap *)
    let r = 
      if check_sat then Inf.infer_heap_nodes estate rhs rhs_rest conseq pos
      else None in 
    begin
      match r with
        | Some (new_iv,new_rn,dead_iv) -> 
              (* let _ = Debug.devel_pprint ("\n inferring_inst_rhs:"^(Cprinter.string_of_h_formula new_rn)^ "\n\n")  pos in *)
              (* let new_p = if CP.isConstTrue new_p then [] else [new_p] in *)
              let new_estate = 
                {estate with 
                    es_infer_vars = new_iv; 
                    es_infer_vars_dead = dead_iv@estate.es_infer_vars_dead; 
                    es_formula = CF.normalize_combine_heap estate.es_formula new_rn;
                    (* es_infer_heap = estate.es_infer_heap@[new_rn]; *)
                    (* es_infer_pure = estate.es_infer_pure@(if CP.isConstTrue new_p then [] else [new_p]); *)
                } 
              in
              (* let fml,_,_,_ = xpure prog new_estate.es_formula in *)
              (* let fml = MCP.pure_of_mix fml in *)
              (* if TP.is_sat_raw fml then *)
              (* add xpure0 of inferred heap to es_infer_pre_thus *)
              let (mf,_,_,_) = xpure_heap_symbolic prog new_rn 0 in
              let inv_f = MCP.pure_of_mix mf in
              let new_estate = add_infer_pure_thus_estate inv_f new_estate in
              let ctx1 = (Ctx new_estate) in
			  let ctx1 = set_unsat_flag ctx1 true in
			  let r1, prf = heap_entail_one_context prog is_folding ctx1 conseq pos in
              (* let r1 = add_infer_pure_to_list_context new_p r1 in *)
              let r1 = add_infer_heap_to_list_context [new_rn] r1 in
              (r1,prf)
                  (* else *)
                  (*   let lhs_xpure,_,_,_ = xpure prog estate.es_formula in *)
                  (*   let rhs_xpure,_,_,_ = xpure prog conseq in *)
                  (*   (\* let _ = print_endline ("WN conseq:"^(Cprinter.string_of_formula conseq)) in *\) *)
                  (*   let r = Inf.infer_pure_m 2 estate lhs_xpure rhs_xpure pos in ( *)
                  (*       match r with *)
                  (*         | Some (new_estate,pf) -> *)
                  (*               let ctx1 = (Ctx new_estate) in *)
                  (*               let ctx1 = set_unsat_flag ctx1 true in *)
                  (*               let r1, prf = heap_entail_one_context prog is_folding ctx1 conseq pos in *)
                  (*               let r1 = add_infer_pure_to_list_context (pf::new_p) r1 in *)
                  (*               let r1 = add_infer_heap_to_list_context [new_rn] r1 in *)
                  (*               (r1,prf) *)
                  (*         | None -> (CF.mkFailCtx_in (Basic_Reason (mkFailContext "unmatched_rhs_data_node" estate (Base rhs_b) None pos, *)
                  (*           CF.mk_failure_bot ("Cannot infer heap and pure"))), NoAlias)  *)
                  (*   ) *)
                  (*                                                                    (\*  let s = "15.4 no match for rhs data node: " ^ (CP.string_of_spec_var  *\) *)
                  (*                                                                    (\*   (CF.get_ptr_from_data rhs)) ^ " (may-bug)." *\) *)
                  (*                                                                    (\* in *\) *)
                  (*                                                                    (\* (\\* Empty the action stack *\\) *\) *)
                  (*                                                                    (\* Context.must_action_stk # override_stk []; *\) *)
                  (*                                                                    (\* (CF.mkFailCtx_in (Basic_Reason (mkFailContext s estate (Base rhs_b) None pos, *\) *)
                  (*                                                                    (\*   CF.mk_failure_may (" Inferred heap made contradiction"))), NoAlias)  *\) *)
        | None ->
              (CF.mkFailCtx_in (Basic_Reason (mkFailContext "infer_heap_node" estate (Base rhs_b) None pos,
              CF.mk_failure_must ("Cannot infer heap and pure 2") sl_error)), NoAlias) 
    end

and do_unmatched_rhs rhs rhs_rest caller prog estate conseq lhs_b rhs_b a (rhs_h_matched_set:CP.spec_var list) is_folding pos = 
 (* let lhs_xpure,_,_,_ = xpure prog estate.es_formula in*)

 (*                      let rhs_xpure,_,_,_ = xpure prog conseq in*)
 (* let r = Inf.infer_pure_m 3 estate lhs_xpure rhs_xpure pos in *)
 (* Thai: change back to Inf.infer_pure *)
 (* let r = Inf.infer_lhs_contra_estate estate lhs_xpure pos in*)
 (* match r with*)
 (* | Some new_estate ->*)
          (* explicitly force unsat checking to be done here *)
    (*      let ctx1 = (elim_unsat_es_now prog (ref 1) new_estate) in*)
          (* let ctx1 = set_unsat_flag ctx1 false in  *)
    (*     let r1, prf = heap_entail_one_context prog is_folding ctx1 conseq pos in*)
    (* (r1,prf) *)
  (*  | None ->*)
          begin
            let (mix_rf,br,rsvl,mem_rf) = xpure_heap_symbolic prog rhs_b.formula_base_heap 0 in
            (* let _ = print_flush "UNMATCHED RHS" in *)
            let filter_redundant a c = CP.simplify_filter_ante TP.simplify_always a c in
            (*get list of pointers which equal NULL*)
            let lhs_eqs = MCP.ptr_equations_with_null lhs_b.CF.formula_base_pure in
            let lhs_p = List.fold_left
              (fun a (b,c) -> CP.mkAnd a (CP.mkPtrEqn b c no_pos) no_pos) (CP.mkTrue no_pos) lhs_eqs in
            let rhs_p = CP.mkNull (CF.get_ptr_from_data rhs) no_pos in
            (*all LHS = null |- RHS != null*)
            if (simple_imply lhs_p rhs_p) then
              let new_lhs_p = filter_redundant lhs_p rhs_p in
              let new_rhs_p = CP.mkNeqNull (CF.get_ptr_from_data rhs) no_pos in
              let s = "15.1" ^ (Cprinter.string_of_pure_formula new_lhs_p) ^ " |- " ^
                (Cprinter.string_of_pure_formula new_rhs_p) ^ " (must-bug)." in
              (*change to must flow*)
              let new_estate = {estate  with CF.es_formula = CF.substitute_flow_into_f
                      !error_flow_int estate.CF.es_formula} in
              (Basic_Reason (mkFailContext s new_estate (Base rhs_b) None pos,
              CF.mk_failure_must s Globals.logical_error), NoAlias)
            else
              begin
                (*check disj memset*)
                let r = ref (-9999) in
                (*
                  example 19 of err2.slk should be handled here.
                  checkentail x::node<_,null> & x=y |- x::node<_,_>*y::node<_,_>
                  - add disjoint pointers into LHS pure formula
                  - for example if RHS contains {x,y}, the constraint x!=y will be added to LHS pure formula
                *)
                let rhs_disj_set_p = CP.mklsPtrNeqEqn
                  (rsvl @ (Gen.BList.remove_dups_eq (CP.eq_spec_var) rhs_h_matched_set)) no_pos in
                (*use global information here*)
                let rhs_disj_set_p =
                  match rhs_disj_set_p with
                    | Some p1 -> p1
                    | _ -> CP.mkTrue no_pos
                in
                let rhs_neq_nulls = CP.mkNeqNull (CF.get_ptr_from_data rhs) no_pos in
                let rhs_mix_p = MCP.memoise_add_pure_N rhs_b.formula_base_pure rhs_disj_set_p in
                let rhs_mix_p_withlsNull = MCP.memoise_add_pure_N rhs_mix_p rhs_neq_nulls in
                let rhs_p = MCP.pure_of_mix rhs_mix_p_withlsNull in
                (*contradiction on RHS?*)
                if not(TP.is_sat_sub_no rhs_p r) then
                  (*contradiction on RHS*)
                  let msg = "contradiction in RHS:" ^ (Cprinter.string_of_pure_formula rhs_p) in
                  let new_estate = {estate  with CF.es_formula = CF.substitute_flow_into_f
                          !error_flow_int estate.CF.es_formula} in
                  (Basic_Reason (mkFailContext msg new_estate (Base rhs_b) None pos,
                  mk_failure_must ("15.2 " ^ msg ^ " (must-bug).") logical_error), NoAlias)
                else
                  let lhs_p = MCP.pure_of_mix lhs_b.formula_base_pure in
                  (*
                    rhs_disj_set != null has been checked above. Separately check for better error classifying.
                  *)
                  if not(simple_imply lhs_p rhs_p) then
                    (*should check may-must here*)
                    let (fc, (contra_list, must_list, may_list)) = check_maymust_failure lhs_p rhs_p in
                    let new_estate = {
                        estate with es_formula =
                            match fc with
                              | CF.Failure_Must _ -> CF.substitute_flow_into_f !error_flow_int estate.es_formula
                              | CF.Failure_May _ -> CF.substitute_flow_into_f !top_flow_int estate.es_formula
                                    (* this denotes a maybe error *)
                              | CF.Failure_Bot _
                              | CF.Failure_Valid -> estate.es_formula
                    } in
                    let fc_template = mkFailContext "" new_estate (Base rhs_b) None pos in
                     let olc = build_and_failures 3 "15.3 no match for rhs data node: "
                       Globals.logical_error (contra_list, must_list, may_list) fc_template in
                     let lc =
                       ( match olc with
                         | FailCtx ft -> ft
                         | SuccCtx _ -> report_error no_pos "solver.ml:M_unmatched_rhs_data_node"
                       )
                     in (lc,Failure)
                  else
                    let s = "15.4 no match for rhs data node: " ^ (CP.string_of_spec_var (CF.get_ptr_from_data rhs))
                      ^ " (may-bug)."in
                    let new_estate = {estate  with CF.es_formula = CF.substitute_flow_into_f
                            !top_flow_int estate.CF.es_formula} in
                    (Basic_Reason (mkFailContext s new_estate (Base rhs_b) None pos,
                    CF.mk_failure_may s logical_error), NoAlias)
              end
          end

and process_unfold prog estate conseq a is_folding pos has_post pid =
  let pr1 = Context.string_of_action_res_simpl in
  let pr2 x = Cprinter.string_of_list_context_short (fst x) in
  (*let pr3 = Cprinter.string_of_spec_var_list in*)
  Debug.no_2 "process_unfold" pr1 Cprinter.string_of_entail_state pr2
      (fun __ _ -> 
          (* print_string "sta\n"; flush(stdout);  *)
          let r = process_unfold_x prog estate conseq a is_folding pos has_post pid in
          (* print_string "sto\n";  *)
          (* flush(stdout); *)
          r)
      a estate 

and init_para lhs_h rhs_h lhs_aset prog pos = match (lhs_h, rhs_h) with
  | DataNode dl, DataNode dr -> 
    let alias = dl.h_formula_data_node::(CP.EMapSV.find_equiv_all dl.h_formula_data_node lhs_aset) in
    if List.mem dr.h_formula_data_node alias then
      try List.map2 (fun v1 v2 -> CP.mkEqVar v1 v2 pos) dl.h_formula_data_arguments dr.h_formula_data_arguments
      with Invalid_argument _ -> []
    else []
  | ViewNode vl, ViewNode vr -> 
    let alias = vl.h_formula_view_node::(CP.EMapSV.find_equiv_all vl.h_formula_view_node lhs_aset) in
    if List.mem vr.h_formula_view_node alias then
      try List.map2 (fun v1 v2 -> CP.mkEqVar v1 v2 pos) vl.h_formula_view_arguments vr.h_formula_view_arguments
      with Invalid_argument _ -> []
    else []
  | _ -> []

and process_action_x caller prog estate conseq lhs_b rhs_b a (rhs_h_matched_set:CP.spec_var list) is_folding pos = 
  if not(Context.is_complex_action a) then
    begin
      Debug.devel_zprint (lazy ("process_action :"
      ^ "\n ### action = " ^ (Context.string_of_action_res a)
      ^ "\n ### estate = " ^ ( Cprinter.string_of_entail_state_short estate)
      ^ "\n ### conseq = " ^ (Cprinter.string_of_formula conseq)
      ^ "\n\n"))  pos 
    end;
    (*add tracing into the entailment state*)
    let action_name:string = Context.string_of_action_res_simpl a in
    (* match a with *)
    (*   | Context.Undefined_action e -> "Undefined_action" *)
    (*   | Context.M_match e -> "Match" *)
    (*   | Context.M_fold e ->  "Fold" *)
    (*   | Context.M_unfold (e,i) -> ("Unfold "^(string_of_int i)) *)
    (*   | Context.M_base_case_unfold e ->  "Base case unfold" *)
    (*   | Context.M_base_case_fold e ->   "Base case fold" *)
    (*   | Context.M_rd_lemma e ->  "Right distributive lemma" *)
    (*   | Context.M_lemma (e,s) ->  ("lemma(" ^ (match s with | None -> "any lemma" | Some c-> (Cprinter.string_of_coercion_type c.coercion_type)^" "^c.coercion_name) ^ ")") *)
    (*   | Context.M_Nothing_to_do s ->  ("Nothing "^s) *)
    (*   | Context.M_unmatched_rhs_data_node (h,_) ->  ("Unmatched RHS data node") *)
    (*   | Context.Seq_action l -> "seq" *)
    (*   | Context.Cond_action l -> "Cond" *)
    (*   | Context.Search_action l -> "search" *)
    (*   | Context.M_lhs_case l -> "lhs_case" *)
    (* in *)
    let estate = {estate with es_trace = action_name::estate.es_trace} in
    let r1,r2 = match a with
      | Context.M_match {
            Context.match_res_lhs_node = lhs_node;
            Context.match_res_lhs_rest = lhs_rest;
            Context.match_res_rhs_node = rhs_node;
            Context.match_res_rhs_rest = rhs_rest;} ->
            let subsumes, to_be_proven = prune_branches_subsume(*_debug*) prog lhs_node rhs_node in
		    if not subsumes then  (CF.mkFailCtx_in (Basic_Reason (mkFailContext "there is a mismatch in branches " estate conseq (get_node_label rhs_node) pos, CF.mk_failure_must "mismatch in branches" sl_error)), NoAlias)
            else
              let new_estate = {estate with es_formula = Base{lhs_b with formula_base_heap = lhs_rest}} in
			  (*TODO: if prunning fails then try unsat on each of the unprunned branches with respect to the context,
			    if it succeeds and the flag from to_be_proven is true then make current context false*)
              let rhs_p = match to_be_proven with
                | None -> rhs_b.formula_base_pure
                | Some (p,_) -> MCP.memoise_add_pure rhs_b.formula_base_pure p in
              let n_rhs_b = Base {rhs_b with formula_base_heap = rhs_rest;formula_base_pure = rhs_p} in
              let res_es0, prf0 = do_match prog new_estate lhs_node rhs_node n_rhs_b rhs_h_matched_set is_folding pos in
              (*if (!exhaust_match) then 
                (match (return_base_cases prog rhs_node n_rhs_b pos) with
                | None -> (res_es0,prf0)
                | Some s ->         
              (*let res_es2, prf2 = heap_entail_conjunct prog is_folding  (Ctx impl_to_expl estate v2) s pos in*)
                (list_context_union res_es2 res_es0, Prooftracer.Unknown))
                else (res_es0,prf0)*)
              (res_es0,prf0)
      | Context.M_fold {
            Context.match_res_rhs_node = rhs_node;
            Context.match_res_rhs_rest = rhs_rest;} -> 
            let estate =
              if Inf.no_infer_rel estate then estate
              else 
                let lhs_h,lhs_p,_,_, _ = CF.split_components estate.es_formula in
                let lhs_alias = MCP.ptr_equations_without_null lhs_p in
                let lhs_aset = CP.EMapSV.build_eset lhs_alias in
                (* Assumed lhs_h to be star or view_node or data_node *)
                let lhs_h_list = split_star_conjunctions lhs_h in
                let init_pures = List.concat (List.map (fun l -> init_para l rhs_node lhs_aset prog pos) lhs_h_list) in
                let init_pure = CP.conj_of_list init_pures pos in
                {estate with es_formula = CF.normalize 1 estate.es_formula (CF.formula_of_pure_formula init_pure pos) pos} 
            in
            do_full_fold prog estate conseq rhs_node rhs_rest rhs_b is_folding pos

      | Context.M_unfold ({Context.match_res_lhs_node=lhs_node},unfold_num) -> 
            let lhs_var = get_node_var lhs_node in
            (* WN : why is there a need for es_infer_invs *)
            (*let estate =  Inf.infer_for_unfold prog estate lhs_node pos in*)
            let curr_unfold_num = (get_view_unfold_num lhs_node)+unfold_num in
            if (curr_unfold_num>1) then 
              (CF.mkFailCtx_in(Basic_Reason(mkFailContext "ensuring finite unfold" estate conseq (get_node_label lhs_node) pos,
              CF.mk_failure_must "infinite unfolding" Globals.sl_error)),NoAlias)
            else
              let delta1 = unfold_nth 1 (prog,None) estate.es_formula lhs_var true unfold_num pos in (* update unfold_num *)
              let ctx1 = build_context (Ctx estate) delta1 pos in
              (* let ctx1 = elim_unsat_ctx_now prog (ref 1) ctx1 in *)
              (* let ctx1 = set_unsat_flag ctx1 true in *)
              let rec prune_helper c =
                match c with
                  | OCtx (c1,c2) -> OCtx(prune_helper c1, prune_helper c2)
                  | Ctx es -> Ctx ({es with es_formula = prune_preds prog true es.es_formula})
              in
        (* TODO: prune_helper slows down the spaguetti benchmark *)
			  let res_rs, prf1 = heap_entail_one_context prog is_folding (* (prune_helper ctx1) *) ctx1 conseq pos in
			  let prf = mkUnfold (Ctx estate) conseq lhs_node prf1 in
			  (res_rs, prf)

      | Context.M_base_case_unfold {
            Context.match_res_lhs_node = lhs_node;
            Context.match_res_rhs_node = rhs_node;}->
            let estate =
              if Inf.no_infer_rel estate then estate
              else 
                let lhs_h,lhs_p,_,_, _ = CF.split_components estate.es_formula in
                let lhs_alias = MCP.ptr_equations_without_null lhs_p in
                let lhs_aset = CP.EMapSV.build_eset lhs_alias in
                (* Assumed lhs_h to be star or view_node or data_node *)
                let lhs_h_list = split_star_conjunctions lhs_h in
                let init_pures = List.concat (List.map (fun l -> init_para l rhs_node lhs_aset prog pos) lhs_h_list) in
                let init_pure = CP.conj_of_list init_pures pos in
                {estate with es_formula = CF.normalize 1 estate.es_formula (CF.formula_of_pure_formula init_pure pos) pos}
            in
            let ans = do_base_case_unfold_only prog estate.es_formula conseq estate lhs_node rhs_node is_folding pos rhs_b in
            (match ans with
              | None -> (CF.mkFailCtx_in(Basic_Reason(mkFailContext "base_case_unfold failed" estate conseq (get_node_label rhs_node) pos
                    , CF.mk_failure_must "base case unfold failed" Globals.sl_error)),NoAlias)
                    (*use UNION, so return MUST, final res = latter case*)
              | Some x -> x)
      | Context.M_base_case_fold {
            Context.match_res_rhs_node = rhs_node;
            Context.match_res_rhs_rest = rhs_rest;} ->
            let estate =
              if Inf.no_infer_rel estate then estate
              else 
                let lhs_h, lhs_p, _,_, _ = CF.split_components estate.es_formula in
                let lhs_alias = MCP.ptr_equations_without_null lhs_p in
                let lhs_aset = CP.EMapSV.build_eset lhs_alias in
                (* Assumed lhs_h to be star or view_node or data_node *)
                let lhs_h_list = split_star_conjunctions lhs_h in
                let init_pures = List.concat (List.map (fun l -> init_para l rhs_node lhs_aset prog pos) lhs_h_list) in
                let init_pure = CP.conj_of_list init_pures pos in
                let new_ante = CF.normalize 1 estate.es_formula (CF.formula_of_pure_formula init_pure pos) pos in
                {estate with es_formula = new_ante} 
            in
            if (estate.es_cont != []) then 
	          (* let  _ = print_string ("rhs_rest = " ^(Cprinter.string_of_h_formula rhs_rest)^ "base = " ^ (Cprinter.string_of_formula (Base rhs_b)) ^ "\n") in  *)
	          (CF.mkFailCtx_in (ContinuationErr (mkFailContext "try the continuation" estate (*(Base rhs_b)*) (Cformula.formula_of_heap rhs_rest pos)  (get_node_label rhs_node) pos)), NoAlias)
            else
              (* NO inference for base-case fold *)
              (* Removal of all vars seems to be strong *)
              (* Maybe only the root of view_node *)
              (*              let rt = Inf.get_args_h_formula rhs_node in                                                          *)
              (*              let rt = match rt with                                                                               *)
              (*                | None -> []                                                                                       *)
              (*                | Some (r,args,_,_) ->                                                                             *)
              (*                      let lhs_als = Inf.get_alias_formula estate.es_formula in                                     *)
              (*                      let lhs_aset = Inf.build_var_aset lhs_als in                                                 *)
              (*                      (* Alias of r *)                                                                             *)
              (*                      let alias = CP.EMapSV.find_equiv_all r lhs_aset in                                           *)
              (*                      let h,_,_,_,_ = CF.split_components estate.es_formula in                                     *)
              (*                      (* Args of viewnodes whose roots are alias of r *)                                           *)
              (*                      let arg_other = Inf.get_all_args alias h in                                                  *)
              (*                      (* Alias of args *)                                                                          *)
              (*                      let alias_all = List.concat (List.map (fun a -> CP.EMapSV.find_equiv_all a lhs_aset) args) in*)
              (*                      (* All the args related to the viewnode of interest *)                                       *)
              (*                      [r] @ args @ alias @ alias_all @ arg_other                                                   *)
              (*              in                                                                                                   *)
              (* moved into do_base_fold *)
              (* let (estate,iv) = Inf.remove_infer_vars_all estate (\* rt *\)in *)
              let (cl,prf) = do_base_fold prog estate conseq rhs_node rhs_rest rhs_b is_folding pos 
              in (cl,prf)
                     (* (Inf.restore_infer_vars iv cl,prf) *)
      | Context.M_lhs_case {
            Context.match_res_lhs_node = lhs_node;
            Context.match_res_rhs_node = rhs_node;}->
            (* let _ = print_string ("process_action: Context.M_lhs_case"  *)
            (*                       ^ "\n\n") in *)
            let ans = do_lhs_case prog estate.es_formula conseq estate lhs_node rhs_node is_folding pos in
            (match ans with
              | None -> (CF.mkFailCtx_in(Basic_Reason(mkFailContext "lhs_case failed" estate conseq (get_node_label rhs_node) pos
                    , CF.mk_failure_must "lhs case analysis failed" Globals.sl_error)),NoAlias)
              | Some x -> x)

      | Context.M_rd_lemma {
            Context.match_res_lhs_node = lhs_node;
            Context.match_res_lhs_rest = lhs_rest;
            Context.match_res_rhs_node = rhs_node;
            Context.match_res_rhs_rest = rhs_rest;
        } -> 
            let r1,r2 = do_coercion prog None estate conseq lhs_rest rhs_rest lhs_node lhs_b rhs_b rhs_node is_folding pos in
            (r1,Search r2)
      | Context.M_lemma  ({
            Context.match_res_lhs_node = lhs_node;
            Context.match_res_lhs_rest = lhs_rest;
            Context.match_res_rhs_node = rhs_node;
            Context.match_res_rhs_rest = rhs_rest;
        },ln) ->
            (* let _ = match ln with *)
            (*   | None -> ()  *)
            (*   | Some c -> ()(\* print_string ("!!! do_coercion should try directly lemma: "^c.coercion_name^"\n") *\) in *)
            let r1,r2 = do_coercion prog ln estate conseq lhs_rest rhs_rest lhs_node lhs_b rhs_b rhs_node is_folding pos in
            (r1,Search r2)
      | Context.Undefined_action mr -> (CF.mkFailCtx_in (Basic_Reason (mkFailContext "undefined action" estate (Base rhs_b) None pos, CF.mk_failure_must "undefined action" Globals.sl_error)), NoAlias)
      | Context.M_Nothing_to_do s -> (CF.mkFailCtx_in (Basic_Reason (mkFailContext s estate (Base rhs_b) None pos,
        CF.mk_failure_must ("Nothing_to_do?"^s) Globals.sl_error)), NoAlias)
            (* to Thai : please move inference code from M_unmatched_rhs here
               and then restore M_unmatched_rhs to previous code without
               any inference *)
      | Context.M_infer_heap (rhs,rhs_rest) ->
            do_infer_heap rhs rhs_rest caller prog estate conseq lhs_b rhs_b a (rhs_h_matched_set:CP.spec_var list) is_folding pos 
                (* (CF.mkFailCtx_in (Basic_Reason (mkFailContext "infer_heap not yet implemented" estate (Base rhs_b) None pos, *)
                (* CF.mk_failure_bot ("infer_heap .. "))), NoAlias) *)
      | Context.M_unmatched_rhs_data_node (rhs,rhs_rest) ->
          (*  do_unmatched_rhs rhs rhs_rest caller prog estate conseq lhs_b rhs_b a (rhs_h_matched_set:CP.spec_var list) is_folding pos *)
                (*      let _,lhs_p,_,_,_ = CF.split_components (estate.es_formula) in              *)
                (*      let lhs_xpure = lhs_p in                                                    *)
                (*      let rhs_xpure,_,_,_ = xpure prog conseq in                                  *)
                (*      let r = Inf.infer_pure estate lhs_xpure rhs_xpure true pos in               *)
                (*      begin                                                                       *)
                (*        match r with                                                              *)
                (*        | Some (new_p, new_estate) ->                                             *)
                (*          let ctx1 = (Ctx new_estate) in                                          *)
                (*          let ctx1 = set_unsat_flag ctx1 true in                                  *)
                (*          let r1, prf = heap_entail_one_context prog is_folding ctx1 conseq pos in*)
                (*          (r1,prf)                                                                *)
                (*        | None -> (                                                               *)
                (* let r = Inf.infer_heap_nodes estate rhs rhs_rest conseq in  *)
                (* begin *)
                (*   match r with *)
                (*     | Some (new_iv,new_rn,new_p) ->  *)
                (*           let _ = Debug.devel_pprint ("\n inferring_inst_rhs:"^(Cprinter.string_of_h_formula new_rn)^ "\n\n")  pos in *)
                (*           let new_estate =  *)
                (*             {estate with  *)
                (*                 es_infer_vars = new_iv;  *)
                (*                 es_formula = CF.normalize_combine_heap estate.es_formula new_rn; *)
                (*                 es_infer_heap = estate.es_infer_heap@[new_rn]; *)
                (*                 es_infer_pure = estate.es_infer_pure@(if CP.isConstTrue new_p then [] else [new_p]); *)
                (*             }  *)
                (*           in *)
                (*           let fml,_,_,_ = xpure prog new_estate.es_formula in *)
                (*           let fml = MCP.pure_of_mix fml in *)
                (*           if Omega.is_sat fml "0" then *)
                (*             let ctx1 = (Ctx new_estate) in *)
			    (*             let ctx1 = set_unsat_flag ctx1 true in *)
			    (*             let r1, prf = heap_entail_one_context prog is_folding ctx1 conseq pos in *)
                (*             (r1,prf) *)
                (*           else *)
                (*             let lhs_xpure,_,_,_ = xpure prog estate.es_formula in *)
                (*             let rhs_xpure,_,_,_ = xpure prog conseq in *)
                (*             (\* let _ = print_endline ("WN conseq:"^(Cprinter.string_of_formula conseq)) in *\) *)
                (*             let r = Inf.infer_pure_m 2 estate lhs_xpure rhs_xpure pos in ( *)
                (*                 match r with *)
                (*                   | Some new_estate -> *)
                (*                         let ctx1 = (Ctx new_estate) in *)
                (*                         let ctx1 = set_unsat_flag ctx1 true in *)
                (*                         let r1, prf = heap_entail_one_context prog is_folding ctx1 conseq pos in *)
                (*                         (r1,prf) *)
                (*                   | None -> (CF.mkFailCtx_in (Basic_Reason (mkFailContext "unmatched_rhs_data_node" estate (Base rhs_b) None pos, *)
                (*                     CF.mk_failure_bot ("Cannot infer heap and pure"))), NoAlias)  *)
                (*             ) *)
                (*                                                                              (\*  let s = "15.4 no match for rhs data node: " ^ (CP.string_of_spec_var  *\) *)
                (*                                                                              (\*   (CF.get_ptr_from_data rhs)) ^ " (may-bug)." *\) *)
                (*                                                                              (\* in *\) *)
                (*                                                                              (\* (\\* Empty the action stack *\\) *\) *)
                (*                                                                              (\* Context.must_action_stk # override_stk []; *\) *)
                (*                                                                              (\* (CF.mkFailCtx_in (Basic_Reason (mkFailContext s estate (Base rhs_b) None pos, *\) *)
                (*                                                                              (\*   CF.mk_failure_may (" Inferred heap made contradiction"))), NoAlias)  *\) *)
                (*     | None -> *)
                (*           let lhs_xpure,_,_,_ = xpure prog estate.es_formula in *)
                (*           (\*                      let rhs_xpure,_,_,_ = xpure prog conseq in*\) *)
                (*           (\* let r = Inf.infer_pure_m 3 estate lhs_xpure rhs_xpure pos in *\) *)
                (*           (\* Thai: change back to Inf.infer_pure *\) *)
                (*           let r = Inf.infer_lhs_contra_estate estate lhs_xpure pos in *)
                (*           begin *)
                (*             match r with *)
                (*               | Some new_estate -> *)
                (*                     (\* explicitly force unsat checking to be done here *\) *)
                (*                     let ctx1 = (elim_unsat_es_now prog (ref 1) new_estate) in *)
                (*                     (\* let ctx1 = set_unsat_flag ctx1 false in  *\) *)
                (*                     let r1, prf = heap_entail_one_context prog is_folding ctx1 conseq pos in *)
                (*                     (r1,prf) *)
                (*               | None -> *)
                (*                     ( *)
                (*                         (\* TODO : obtain xpure0 of RHS *)
                (*                            (i) check if it is unsat, or *)
                (*                            (ii) check if negated term implied by LHS *)
                (*                         *\) *)
                (*                         (\* check LHS to see if null -> must error else may error *\) *)
                (*                         let (mix_rf,br,rsvl,mem_rf) = xpure_heap_symbolic prog rhs_b.formula_base_heap 0 in *)
                (*                         (\* let _ = print_flush "UNMATCHED RHS" in *\) *)
                (*                         (\* *)
                (*                         (\*let (mix_lf,bl,lsvl,mem_lf) = xpure_heap_symbolic prog lhs_b.formula_base_heap 0 in*\) *)
                (*                           let pr = Cprinter.string_of_spec_var_list in *)
                (*                           let _ = print_flush "UNMATCHED RHS" in *)
                (*                           let _ = print_flush ("LHS :"^(Cprinter.string_of_formula (Base lhs_b))) in *)
                (*                           let _ = print_flush ("RHS :"^(Cprinter.string_of_formula (Base rhs_b))) in *)
                (*                         (\* let _ = print_flush ("RHS - data :"^(Cprinter.string_of_h_formula rhs)) in *\) *)
                (*                           let _ = print_flush ("RHS - xpure (mix_f) :"^(Cprinter.string_of_mix_formula mix_rf)) in *)
                (*                           let _ = print_flush ("RHS - xpure (svl) :"^(pr rsvl)) in *)
                (*                           let _ = print_flush ("RHS - xpure (mem_f) :"^(pr_list pr mem_rf.mem_formula_mset)) in *)
                (*                         *\) *)
                (*                         let filter_redundant a c = CP.simplify_filter_ante TP.simplify_always a c in *)
                (*                         (\*get list of pointers which equal NULL*\) *)
                (*                         let lhs_eqs = MCP.ptr_equations_with_null lhs_b.CF.formula_base_pure in *)
                (*                         let lhs_p = List.fold_left *)
                (*                           (fun a (b,c) -> CP.mkAnd a (CP.mkPtrEqn b c no_pos) no_pos) (CP.mkTrue no_pos) lhs_eqs in *)
                (*                         let rhs_p = CP.mkNull (CF.get_ptr_from_data rhs) no_pos in *)
                (*                         (\*all LHS = null |- RHS != null*\) *)
                (*                         if (simple_imply lhs_p rhs_p) then *)
                (*                           let new_lhs_p = filter_redundant lhs_p rhs_p in *)
                (*                           let new_rhs_p = CP.mkNeqNull (CF.get_ptr_from_data rhs) no_pos in *)
                (*                           let s = "15.1" ^ (Cprinter.string_of_pure_formula new_lhs_p) ^ " |- " ^ *)
                (*                             (Cprinter.string_of_pure_formula new_rhs_p) ^ " (must-bug)." in *)
                (*                           (\*change to must flow*\) *)
                (*                           let new_estate = {estate  with CF.es_formula = CF.substitute_flow_into_f *)
                (*                                   !error_flow_int estate.CF.es_formula} in *)
                (*                           (CF.mkFailCtx_in (Basic_Reason (mkFailContext s new_estate (Base rhs_b) None pos, *)
                (*                           CF.mk_failure_must s Globals.sl_error)), NoAlias) *)
                (*                         else *)
                (*                           begin *)
                (*                             (\*check disj memset*\) *)
                (*                             let r = ref (-9999) in *)
                (*                             (\* *)
                (*                               example 19 of err2.slk should be handled here. *)
                (*                               checkentail x::node<_,null> & x=y |- x::node<_,_>*y::node<_,_> *)
                (*                               - add disjoint pointers into LHS pure formula *)
                (*                               - for example if RHS contains {x,y}, the constraint x!=y will be added to LHS pure formula *)
                (*                             *\) *)
                (*                             let rhs_disj_set_p = CP.mklsPtrNeqEqn *)
                (*                               (rsvl @ (Gen.BList.remove_dups_eq (CP.eq_spec_var) rhs_h_matched_set)) no_pos in *)
                (*                             (\*use global information here*\) *)
                (*                             let rhs_disj_set_p = *)
                (*                               match rhs_disj_set_p with *)
                (*                                 | Some p1 -> p1 *)
                (*                                 | _ -> CP.mkTrue no_pos *)
                (*                             in *)
                (*                             let rhs_neq_nulls = CP.mkNeqNull (CF.get_ptr_from_data rhs) no_pos in *)
                (*                             let rhs_mix_p = MCP.memoise_add_pure_N rhs_b.formula_base_pure rhs_disj_set_p in *)
                (*                             let rhs_mix_p_withlsNull = MCP.memoise_add_pure_N rhs_mix_p rhs_neq_nulls in *)
                (*                             let rhs_p = MCP.pure_of_mix rhs_mix_p_withlsNull in *)
                (*                             (\*contradiction on RHS?*\) *)
                (*                             if not(TP.is_sat_sub_no rhs_p r) then *)
                (*                               (\*contradiction on RHS*\) *)
                (*                               let msg = "contradiction in RHS:" ^ (Cprinter.string_of_pure_formula rhs_p) in *)
                (*                               let new_estate = {estate  with CF.es_formula = CF.substitute_flow_into_f *)
                (*                                       !error_flow_int estate.CF.es_formula} in *)
                (*                               (CF.mkFailCtx_in (Basic_Reason (mkFailContext msg new_estate (Base rhs_b) None pos, *)
                (*                               mk_failure_must ("15.2 " ^ msg ^ " (must-bug).") sl_error)), NoAlias) *)
                (*                             else *)
                (*                               let lhs_p = MCP.pure_of_mix lhs_b.formula_base_pure in *)
                (*                               (\* *)
                (*                                 rhs_disj_set != null has been checked above. Separately check for better error classifying. *)
                (*                               *\) *)
                (*                               if not(simple_imply lhs_p rhs_p) then *)
                (*                                 (\*should check may-must here*\) *)
                (*                                 let (fc, (contra_list, must_list, may_list)) = check_maymust_failure lhs_p rhs_p in *)
                (*                                 let new_estate = { *)
                (*                                     estate with es_formula = *)
                (*                                         match fc with *)
                (*                                           | CF.Failure_Must _ -> CF.substitute_flow_into_f !error_flow_int estate.es_formula *)
                (*                                           | CF.Failure_May _ -> CF.substitute_flow_into_f !top_flow_int estate.es_formula *)
                (*                                                 (\* this denotes a maybe error *\) *)
                (*                                           | CF.Failure_Bot _ *)
                (*                                           | CF.Failure_Valid -> estate.es_formula *)
                (*                                 } in *)
                (*                                 let fc_template = mkFailContext "" new_estate (Base rhs_b) None pos in *)
                (*                                 (build_and_failures "15.3" sl_error (contra_list, must_list, may_list) fc_template, UnsatConseq) *)
                (*                               else *)
                (*                                 let s = "15.4 no match for rhs data node: " ^ (CP.string_of_spec_var (CF.get_ptr_from_data rhs)) *)
                (*                                   ^ " (may-bug)."in *)
                (*                                 let new_estate = {estate  with CF.es_formula = CF.substitute_flow_into_f *)
                (*                                         !top_flow_int estate.CF.es_formula} in *)
                (*                                 (CF.mkFailCtx_in (Basic_Reason (mkFailContext s new_estate (Base rhs_b) None pos, *)
                (*                                 CF.mk_failure_may s logical_error)), NoAlias) *)
                (*                           end *)
                (*                     ) *)
                (*           end *)
                (*               (\*          end*\) *)
                (*               (\*          )  *\) *)
                (* end *)
                (*****************************************************************************)
          begin
              let lhs_xpure,_,_,_ = xpure prog estate.es_formula in
              (*                      let rhs_xpure,_,_,_ = xpure prog conseq in*)
              (* let r = Inf.infer_pure_m 3 estate lhs_xpure rhs_xpure pos in *)
              (* Thai: change back to Inf.infer_pure *)
              let msg = "do_unmatched_rhs :"^(Cprinter.string_of_h_formula rhs) in
              let r = Inf.infer_lhs_contra_estate estate lhs_xpure pos msg in
              match r with
                | Some (new_estate,pf) ->
                (* explicitly force unsat checking to be done here *)
                    let ctx1 = (elim_unsat_es_now prog (ref 1) new_estate) in
                (* let ctx1 = set_unsat_flag ctx1 false in  *)
                    let r1, prf = heap_entail_one_context prog is_folding ctx1 conseq pos in
                    let r1 = add_infer_pure_to_list_context [pf] r1 in
                    (r1,prf)
                | None ->
                    begin
                        let s = "15.5 no match for rhs data node: " ^
                          (CP.string_of_spec_var (CF.get_ptr_from_data rhs)) ^ " (must-bug)."in
                        let new_estate = {estate  with CF.es_formula = CF.substitute_flow_into_f
                                !error_flow_int estate.CF.es_formula} in
                        let unmatched_lhs = Basic_Reason (mkFailContext s new_estate (Base rhs_b) None pos,
                                                          CF.mk_failure_must s Globals.sl_error) in
                        let (res_lc, prf) = do_unmatched_rhs rhs rhs_rest caller prog estate conseq lhs_b rhs_b a (rhs_h_matched_set:CP.spec_var list) is_folding pos in
                        (CF.mkFailCtx_in (Or_Reason (res_lc, unmatched_lhs)), prf)
                    end
          end
      | Context.Seq_action l ->
            report_warning no_pos "Sequential action - not handled";
            (CF.mkFailCtx_in (Basic_Reason (mkFailContext "Sequential action - not handled" estate (Base rhs_b) None pos
                , CF.mk_failure_must "sequential action - not handled" Globals.sl_error)), NoAlias)
      | Context.Cond_action l ->
            Debug.ninfo_hprint (add_str "length of cactions" string_of_int) (List.length l) no_pos;
            Debug.ninfo_hprint (add_str "cond action" Context.string_of_action_res_simpl_0) a no_pos;
            let rec helper l = match l with
              | [] ->           
                    (CF.mkFailCtx_in (Basic_Reason (mkFailContext "Cond action - none succeeded" estate (Base rhs_b) None pos
                        , CF.mk_failure_must "Cond action - none succeeded" Globals.sl_error)), NoAlias)
              | [(_,act)] -> process_action 130 prog estate conseq lhs_b rhs_b act rhs_h_matched_set is_folding pos       
              | (_,act)::xs ->
                    let (r,prf) = process_action 131 prog estate conseq lhs_b rhs_b act rhs_h_matched_set is_folding pos in
                    if isFailCtx r then helper xs
                    else (r,prf)
            in helper l
      | Context.Search_action l ->
            Debug.ninfo_hprint (add_str "length of sactions" string_of_int) (List.length l) no_pos;
            Debug.ninfo_hprint (add_str "search action" Context.string_of_action_res_simpl) a no_pos;
            let r = List.map (fun (_,a1) -> process_action 14 prog estate conseq lhs_b rhs_b a1
                rhs_h_matched_set is_folding pos) l in
            let (ctx_lst, pf) = List.fold_left combine_results (List.hd r) (List.tl r) in
            (* List.fold_left combine_results (List.hd r) (List.tl r) in *)
            
            (ctx_lst, pf) in
    if (Context.is_complex_action a) then (r1,r2) else 
      (push_hole_action a r1,r2)

and process_action caller prog estate conseq lhs_b rhs_b a (rhs_h_matched_set:CP.spec_var list) is_folding pos =
  let pr1 = Context.string_of_action_res_simpl in
  let length_ctx ctx = match ctx with
    | CF.FailCtx _ -> 0
    | CF.SuccCtx ctx0 -> List.length ctx0 in
  let pr2 x = "\nctx length:" ^ (string_of_int (length_ctx (fst x))) ^ " \n Context:"^ Cprinter.string_of_list_context_short (fst x) (* ^ "\n Proof: " ^ (Prooftracer.string_of_proof (snd x)) *) in
  (*let pr3 = Cprinter.string_of_spec_var_list in*)
  Debug.no_4 "process_action" string_of_int pr1 Cprinter.string_of_entail_state Cprinter.string_of_formula pr2
      (fun __ _ _ _ -> process_action_x caller prog estate conseq lhs_b rhs_b a
          rhs_h_matched_set is_folding pos) caller a estate conseq

(* let pr1 = Context.string_of_action_res in *)
(* let pr2 x = Cprinter.string_of_list_context_short (fst x) in *)
(* (\*let pr3 = Cprinter.string_of_spec_var_list in*\) *)
(* Debug.loop_1_no "process_action" pr1 pr2 *)
(*     (fun __-> process_action_x prog estate conseq lhs_b rhs_b a *)
(*      rhs_h_matched_set is_folding pos) a *)
      
      
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
   Debug.devel_zprint (lazy ("heap_entail_non_empty_rhs_heap: trying to prove " ^ (Cprinter.string_of_h_formula ln2))) pos;
   

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
   Debug.devel_zprint (lazy ("heap_entail_non_empty_rhs_heap: no aliased node for data node " ^ (Cprinter.string_of_h_formula ln2)^ " is found in LHS\n")) pos;
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
(* Debug.no_2 "check_aliased_node" *)
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
   if (!exhaust_match) then 
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
   (Debug.devel_zprint (lazy ("do_coercion for LHS:" ^ (Cprinter.string_of_h_formula anode) ^" RHS:"^(Cprinter.string_of_h_formula ln2)^ "\n")) pos;
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
   if !use_coercion then 
   begin
(* two different predicates match, try coercion *)
   Debug.devel_zprint (lazy ("heap_entail_non_empty_rhs_heap: " ^ "trying coercion")) pos;
   let res, prfs = do_coercion c1 c2 prog estate conseq ctx0 resth1 resth2 anode (*lhs_p lhs_t lhs_fl lhs_br rhs_p rhs_t rhs_fl*) lhs_b rhs_b ln2 is_folding pos pid in
   let prf = mkCoercion2 ctx0 conseq prfs in
   (res, prf)
   end else 
   begin
   Debug.devel_zprint (lazy ("heap_entail_non_empty_rhs_heap: " ^ "can't reduce, fold, unfold")) pos;
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
   else if !use_coercion then (* there is a match at some node, but not at root *)
   begin
   Debug.devel_zprint (lazy ("heap_entail_non_empty_rhs_heap: there is a match at some node, but not at root\n")) pos;
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
   if !use_set then (* use_set denotes set of state searching *)
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
and do_universal prog estate (node:CF.h_formula) rest_of_lhs coer anode lhs_b rhs_b conseq is_folding pos: (list_context * proof) =
  let pr (e,_) = Cprinter.string_of_list_context e in
  Debug.no_3 "do_universal"  Cprinter.string_of_h_formula Cprinter.string_of_formula Cprinter.string_of_formula pr 
      (fun _ _ _ -> do_universal_x prog estate node rest_of_lhs coer anode lhs_b rhs_b conseq is_folding pos)
      node rest_of_lhs conseq

and do_universal_x prog estate (node:CF.h_formula) rest_of_lhs coer anode lhs_b rhs_b conseq is_folding pos: (list_context * proof) =
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
    let lhs_heap, lhs_guard,lhs_fl, lhs_branches, _  = split_components coer_lhs in
    let lhs_guard = MCP.fold_mem_lst (CP.mkTrue no_pos) false false (* true true *) lhs_guard in
    (*node -> current heap node | lhs_heap -> head of the coercion*)
    match node, lhs_heap with
	  | ViewNode ({ h_formula_view_node = p1;
	    h_formula_view_name = c1;
	    h_formula_view_origins = origs;
	    h_formula_view_remaining_branches = br1;
	    h_formula_view_perm = perm1; (*LDK*)
	    h_formula_view_arguments = ps1} (* as h1 *)),
        ViewNode ({ h_formula_view_node = p2;
	    h_formula_view_name = c2;
	    h_formula_view_remaining_branches = br2;
	    h_formula_view_perm = perm2; (*LDK*)
	    h_formula_view_arguments = ps2} (* as h2 *)) (* when CF.is_eq_view_name(\*is_eq_view_spec*\) h1 h2 (\*c1=c2 && (br_match br1 br2) *\) *)
            (*lemmas can also be applied to data node*)
	  | DataNode ({ h_formula_data_node = p1;
	    h_formula_data_name = c1;
	    h_formula_data_origins = origs;
	    h_formula_data_remaining_branches = br1;
	    h_formula_data_perm = perm1; (*LDK*)
	    h_formula_data_arguments = ps1} (* as h1 *)),
        DataNode ({ h_formula_data_node = p2;
	    h_formula_data_name = c2;
	    h_formula_data_remaining_branches = br2;
	    h_formula_data_perm = perm2; (*LDK*)
	    h_formula_data_arguments = ps2} (* as h2 *)) when CF.is_eq_node_name(*is_eq_view_spec*) c1 c2 (*c1=c2 && (br_match br1 br2) *) ->

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
	        (* if (!lemma_heuristic && 		(\* use coerce&match together with the history mechanism *\) *)
		    (*     (not(apply_coer) 					(\* the target is not present *\) *)
		    (*     (\* or (get_estate_must_match estate) *\))  (\* must match *\) *)
		    (* && (List.mem coer.coercion_body_view origs *)
		    (* or is_cycle_coer coer origs)) (\* there is a cycle *\) *)
		    (*   or 	(not(!lemma_heuristic) &&   (\* use coerce&distribute&match*\) *)
		    (*       (not(apply_coer) or 				(\* the target is not present *\) *)
		    (*           ((\* (get_estate_must_match estate) 	(\\* must match *\\) *\) *)
		    (*           (\* &&  *\)(not(!enable_distribution) 		(\* distributive coercion is not allowed *\) *)
		    (*   	    or not(is_distributive coer))))) 	(\* coercion is not distributive *\) *)
            if (not(apply_coer) or (is_cycle_coer coer origs))
	        then
              (* let s = (pr_list string_of_bool [f1;f3;f4;f5;f6]) in *)
		      (Debug.devel_zprint (lazy("[do_universal]: Coercion cannot be applied!"(* ^s *))) pos; 
		      (CF.mkFailCtx_in(Basic_Reason( { 
				  fc_message ="failed coercion application";
				  fc_current_lhs = estate;
				  fc_prior_steps = estate.es_prior_steps;
				  fc_orig_conseq = estate.es_orig_conseq;
				  fc_current_conseq = CF.formula_of_heap HFalse pos;
				  fc_failure_pts = match (get_node_label node) with | Some s-> [s] | _ -> [];}
                  , CF.mk_failure_must "failed coercion" Globals.sl_error)), Failure))
	        else	(* we can apply coercion *)
		      begin
		        (* if (not(!lemma_heuristic) (\* && get_estate_must_match estate *\)) then *)
		        (*   ((\*print_string("disable distribution\n");*\) enable_distribution := false); *)
		        (* the \rho substitution \rho (B) and  \rho(G) is performed *)
                (*subst perm variable when applicable*)
                let perms1,perms2 =
                  if (Perm.allow_perm ()) then
                    match perm1,perm2 with
                      | Some f1, Some f2 ->
                            ([f1],[f2])
                      | Some f1, None ->
                            ([f1],[full_perm_var])
                      | None, Some f2 ->
                            ([full_perm_var],[f2])
                      | None, None ->
                            ([],[])
                  else
                    ([],[])
                in
                let fr_vars = perms2@(p2 :: ps2)in
                let to_vars = perms1@(p1 :: ps1)in
		        let lhs_guard_new = CP.subst_avoid_capture fr_vars to_vars lhs_guard in
		        let lhs_branches_new = List.map (fun (s, f) -> (s, (CP.subst_avoid_capture fr_vars to_vars f))) lhs_branches in
		        let coer_rhs_new1 = subst_avoid_capture fr_vars to_vars coer_rhs in
                let coer_rhs_new1 =
                  if (Perm.allow_perm ()) then
                    match perm1,perm2 with
                      | Some f1, None ->
                            propagate_perm_formula coer_rhs_new1 f1
                      | _ -> coer_rhs_new1
                  else
                    coer_rhs_new1
                in
		        let coer_rhs_new = add_origins coer_rhs_new1 ((* coer.coercion_name ::  *)origs) in
		        let _ = reset_int2 () in
		        (*let xpure_lhs = xpure prog f in*)
		        (*************************************************************************************************************************************************************************)
		        (* delay the guard check *)
		        (* for now, just add it to the consequent *)
		        (*************************************************************************************************************************************************************************)
		        (* let guard_to_check = CP.mkExists f_univ_vars lhs_guard_new pos in *)
		        (* let _ = print_string("xpure_lhs: " ^ (Cprinter.string_of_pure_formula xpure_lhs) ^ "\n") in *)
		        (* let _ = print_string("WN DO_UNIV guard to conseq: " ^ (Cprinter.string_of_pure_formula lhs_guard_new (\* guard_to_check *\)) ^ "\n") in *)
		        let new_f = normalize_replace (* 8 *) coer_rhs_new rest_of_lhs pos in
		        (* add the guard to the consequent  - however, the guard check is delayed *)
                (* ?? *)
		        let formula,to_aux_conseq = 
                  if !allow_imm then (replace_branches lhs_branches_new (mkTrue (mkTrueFlow ()) pos),lhs_guard_new)
                  else (replace_branches lhs_branches_new (formula_of_pure_N lhs_guard_new pos), CP.mkTrue pos) in
		        let new_conseq = normalize 9 conseq formula pos in
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
	  | _ -> (CF.mkFailCtx_in(Basic_Reason ( { 
			fc_message ="failed coercion application, found data but expected view";
			fc_current_lhs = estate;
			fc_prior_steps = estate.es_prior_steps;
			fc_orig_conseq = estate.es_orig_conseq;
			fc_current_conseq = CF.formula_of_heap HFalse pos;
			fc_failure_pts = [];}
            , CF.mk_failure_must "11" Globals.sl_error)), Failure)
  end


and is_cycle_coer (c:coercion_decl) (origs:ident list) : bool =  
  Debug.no_2 "is_cycle_coer" Cprinter.string_of_coercion Cprinter.str_ident_list string_of_bool
      is_cycle_coer_a c origs

(* this checks if node is being applied a second time with same coercion rule *)
and is_cycle_coer_a (c:coercion_decl) (origs:ident list) : bool =  List.mem c.coercion_name origs

and is_original_match_a anode ln2 = 
  (get_view_original anode) || (get_view_original ln2)

and is_original_match anode ln2 = 
  let p = Cprinter.string_of_h_formula in
  Debug.no_2 "is_original_match"
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
and rewrite_coercion prog estate node f coer lhs_b rhs_b target_b weaken pos : (int * formula) =
  let p1 = Cprinter.string_of_formula in
  let p2 = pr_pair string_of_int Cprinter.string_of_formula in
  Debug.no_4 "rewrite_coercion" Cprinter.string_of_h_formula  p1 Cprinter.string_of_coercion Cprinter.string_of_entail_state
      p2 (fun _ _ _ _ -> rewrite_coercion_x prog estate node f coer lhs_b rhs_b target_b weaken pos) node f coer estate
      (*
        the fst of res: int
        0: false
        1: true & __norm
        2: true & __Error
      *)
      (*LDK: return the a new formula (new_f) after apply coercion into f*)
and rewrite_coercion_x prog estate node f coer lhs_b rhs_b target_b weaken pos : (int * formula) =
  (* This function also needs to add the name and the origin list
     of the source view to the origin list of the target view. It
     needs to check if the target view in coer_rhs belongs to the
     list of origins of node. If so, don't apply the coercion *)
  (******************** here it was the test for coerce&match *************************)
  let coer_lhs = coer.coercion_head in
  let coer_rhs = coer.coercion_body in
  let lhs_heap, lhs_guard, lhs_flow, lhs_branches, _ = split_components coer_lhs in
  let lhs_guard = MCP.fold_mem_lst (CP.mkTrue no_pos) false false (* true true *) lhs_guard in  (* TODO : check with_dupl, with_inv *)

  (* let _ = print_string ("rewrite_coercion_x:" *)
  (*                       ^ "\n ### f = " ^ (Cprinter.string_of_formula f) *)
  (*                       ^ "\n ### coer_lhs = " ^ (Cprinter.string_of_formula coer_lhs) *)
  (*                       ^ "\n ### lhs_heap = " ^ (Cprinter.string_of_h_formula lhs_heap) *)
  (*                       ^ "\n ### coer_rhs = " ^ (Cprinter.string_of_formula coer_rhs) *)
  (*                       ^ "\n ### coer_guard = " ^ (Cprinter.string_of_pure_formula lhs_guard) *)
  (*                       ^ "\n") in *)

  (*SIMPLE lhs*)
  match node, lhs_heap with (*node -> current heap node | lhs_heap -> head of the coercion*)
    | ViewNode ({ h_formula_view_node = p1;
      h_formula_view_imm = imm1;       
      h_formula_view_name = c1;
      h_formula_view_origins = origs;
      (* h_formula_view_original = original; (*LDK: unused*) *)
      h_formula_view_remaining_branches = br1;
      h_formula_view_perm = perm1; (*LDK*)
      h_formula_view_arguments = ps1} (* as h1 *)),
	  ViewNode ({ h_formula_view_node = p2;
      h_formula_view_name = c2;
      h_formula_view_remaining_branches = br2;
      h_formula_view_perm = perm2; (*LDK*)
      h_formula_view_arguments = ps2} (* as h2 *)) 
          (* when CF.is_eq_view_name(\*is_eq_view_spec*\) h1 h2  (\* c1=c2 && (br_match br1 br2) *\)->  *)
          (*lemmas can be applied to data node as well*)
	| DataNode ({ h_formula_data_node = p1;
	  h_formula_data_name = c1;
          h_formula_data_imm = imm1;       
	  h_formula_data_origins = origs;
	  h_formula_data_remaining_branches = br1;
	  h_formula_data_perm = perm1; (*LDK*)
	  h_formula_data_arguments = ps1} (* as h1 *)),
      DataNode ({ h_formula_data_node = p2;
	  h_formula_data_name = c2;
	  h_formula_data_remaining_branches = br2;
	  h_formula_data_perm = perm2; (*LDK*)
	  h_formula_data_arguments = ps2} (* as h2 *)) when CF.is_eq_node_name(*is_eq_view_spec*) c1 c2 (*c1=c2 && (br_match br1 br2) *) ->

          begin
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
	        (* if (!lemma_heuristic &&  *)
            (*     (not(apply_coer) (\* coerce&match+history *\) (\* or (get_estate_must_match estate) *\)) &&  *)
            (*     (List.mem coer.coercion_body_view origs  *)
            (*     or (\* List.mem coer.coercion_head_view origs *\)  (is_cycle_coer coer origs)) *)
            (* ) *)
	        (*   or (not(!lemma_heuristic) && (\* coerce&distribute&match *\) *)
		    (*       (not(apply_coer) or 	(\* the target is not present *\) *)
			(*           (false (\* (get_estate_must_match estate) *\) (\* must match *\) && (not(!enable_distribution) (\* distributive coercion is not allowed *\) *)
			(* 		  or not(is_distributive coer))))) (\* coercion is not distributive *\) *)
            (* when disabled --imm failed and vice-versa! *)
            let flag = if !allow_imm then false else not(apply_coer) in
            if (flag or(is_cycle_coer coer origs))
	        then
              (* let s = (pr_list string_of_bool [f1;(\* f2; *\)f3;f4;f5;f6]) in *)
		      (Debug.devel_zprint (lazy("[rewrite_coercion]: Rewrite cannot be applied!"(* ^s *))) pos; (0, mkTrue (mkTrueFlow ()) no_pos))
	        else
		      (* we can apply coercion *)
		      begin
		        (* apply \rho (G)	and \rho(B) *)
                let perms1,perms2 =
                  if (Perm.allow_perm ()) then
                    match perm1,perm2 with
                      | Some f1, Some f2 ->
                            ([f1],[f2])
                      | Some f1, None ->
                            ([f1],[full_perm_var])
                      | None, Some f2 ->
                            ([full_perm_var],[f2])
                      | None, None ->
                            ([],[])
                  else
                    ([],[])
                in
                let fr_vars = perms2@(p2 :: ps2)in
                let to_vars = perms1@(p1 :: ps1)in
		        let lhs_guard_new = CP.subst_avoid_capture fr_vars to_vars lhs_guard in
		        (*let lhs_branches_new = List.map (fun (s, f) -> (s, (CP.subst_avoid_capture fr_vars to_vars f))) lhs_branches in*)
		        let coer_rhs_new1 = subst_avoid_capture fr_vars to_vars coer_rhs in
                let coer_rhs_new1 =
                  if (Perm.allow_perm ()) then
                    match perm1,perm2 with
                      | Some f1, None ->
                            propagate_perm_formula coer_rhs_new1 f1
                      | _ -> coer_rhs_new1
                  else
                    coer_rhs_new1
                in
		        (* let coer_rhs_new = add_origins coer_rhs_new1 (coer.coercion_head_view :: origs) in *)
	        let coer_rhs_new = add_origins coer_rhs_new1 ((* coer.coercion_name ::  *)origs) in

                (* propagate the immutability annotation inside the definition *)
                let coer_rhs_new = propagate_imm_formula coer_rhs_new imm1 in

                (* Currently, I am trying to change in advance at the trans_one_coer *)
                (* Add origins to the body of the coercion which consists of *)
                (*   several star-conjunction nodes. If there are multiple nodes *)
                (*   with a same name (because of fractional permission). We only *)
                (*   add origins to the first node and leave the rest untouched. *)
                (*   This is to make sure that after a coercion, there will be *)
                (*   a MATCH for the first node. *)
		        (* let coer_rhs_new = add_origins_to_coer coer_rhs_new1 ((\* coer.coercion_name ::  *\)origs) in *)
		        (* let coer_rhs_new = add_origins coer_rhs_new1 ((\* coer.coercion_name ::  *\)origs) in *)
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
                  (*mark __Error case, return 2 or 1*)
		          let new_f = normalize_replace coer_rhs_new f pos in
			      (* if (not(!lemma_heuristic) (\* && get_estate_must_match estate *\)) then *)
			      (*   ((\*print_string("disable distribution\n"); *\)enable_distribution := false); *)
                  let f1 = CF.formula_is_eq_flow coer_rhs_new !error_flow_int in
                  let fst_res =
                    if f1 then 2 else 1
                  in
			      (fst_res, new_f)
		        else if !case_split then begin
                  (*LDK: 
                    - Not yet handle perm in this case
                    - case_split is probably for view nodes only
                  *)
                  match node with
                    | ViewNode h1 ->
		                  (*
		                    Doing case splitting based on the guard.
		                  *)
		                  Debug.devel_pprint ("rewrite_coercion: guard is not satisfied, " ^ "splitting.\n") pos;
		                  let neg_guard = CP.mkNot lhs_guard_new None pos in
                          let node = ViewNode{h1 with h_formula_view_remaining_branches=None; h_formula_view_pruning_conditions=[];} in
		                  let f0 = normalize 10 f (formula_of_heap node pos) pos in
		                  let f1 = normalize 11 f0 (formula_of_mix_formula (MCP.mix_of_pure neg_guard) pos) pos in
			              (* unfold the case with the negation of the guard. *)
		                  let f1 = unfold_nth 2 (prog,None) f1 p1 true 0 pos in
		                  let f2 = normalize 12 f0 (formula_of_mix_formula (MCP.mix_of_pure lhs_guard_new) pos) pos in
			              (* f2 need no unfolding, since next time coercion is reapplied, the guard is guaranteed to be satisified *)
		                  let new_f = mkOr f1 f2 pos in
			              (* if (not(!lemma_heuristic) (\* && (get_estate_must_match estate) *\)) then *)
			              (*   ((\*print_string("disable distribution\n"); *\)enable_distribution := false); *)
			              (1, new_f)
                    | _ -> 
                          let _ = print_string ("[Solver.ml] Warning: This case not yet handled properly \n") in
		                  let new_f = normalize_replace f coer_rhs_new pos in
			              (1, new_f)
		        end else begin
		          Debug.devel_pprint "rewrite_coercion: guard is not satisfied, no splitting.\n" pos;
		          (0, mkTrue (mkTrueFlow ()) no_pos)
		        end
		      end
          end
    | _ -> (0, mkTrue (mkTrueFlow ()) no_pos)
	      (*end	*)

and apply_universal prog estate coer resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 c2 conseq is_folding pos =
  let pr (e,_) = Cprinter.string_of_list_context e in
  Debug.no_3 "apply_universal"  Cprinter.string_of_h_formula Cprinter.string_of_h_formula (fun x -> x) pr 
      (fun _ _ _ -> apply_universal_a prog estate coer resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 c2 conseq is_folding pos)
      anode resth1 c2
      (* anode - chosen node, resth1 - rest of heap *)

(*******************************************************************************************************************************************************************************************)
and apply_universal_a prog estate coer resth1 anode (*lhs_p lhs_t lhs_fl lhs_br*) lhs_b rhs_b c1 c2 conseq is_folding pos =
  (*******************************************************************************************************************************************************************************************)
  let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_br) = CF.extr_formula_base lhs_b in
  flush stdout;
  if Gen.is_empty coer.coercion_univ_vars then (CF.mkFailCtx_in ( Basic_Reason (  {
	  fc_message = "failed apply_universal : not a universal rule";
	  fc_current_lhs = estate;
	  fc_prior_steps = estate.es_prior_steps;
	  fc_orig_conseq = estate.es_orig_conseq;
	  fc_current_conseq = CF.formula_of_heap HFalse pos; 
	  fc_failure_pts = match (get_node_label anode) with | Some s-> [s] | _ -> [];}
      , CF.mk_failure_must "12" Globals.sl_error)), Failure)
  else begin
    let f = mkBase resth1 lhs_p lhs_t lhs_fl lhs_br pos in(* Assume coercions have no branches *)
    let estate = CF.moving_ivars_to_evars estate anode in
    let _ = Debug.devel_zprint (lazy ("heap_entail_non_empty_rhs_heap: apply_universal: "	^ "c1 = " ^ c1 ^ ", c2 = " ^ c2 ^ "\n")) pos in
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
  Debug.no_2 "find_coercions" p1 p1 p2 (fun _ _ -> find_coercions_x c1 c2 prog anode ln2 ) anode ln2

and do_coercion prog c_opt estate conseq resth1 resth2 anode lhs_b rhs_b ln2 is_folding pos : (CF.list_context * proof list) =
  let pr (e,_) = Cprinter.string_of_list_context e in
  Debug.no_5 "do_coercion" (* prid prid  *)Cprinter.string_of_h_formula Cprinter.string_of_h_formula Cprinter.string_of_h_formula 
      Cprinter.string_of_h_formula Cprinter.string_of_formula_base pr
      (fun _ _ _ _ _ -> do_coercion_x prog c_opt estate conseq resth1 resth2 anode lhs_b rhs_b ln2 is_folding pos) anode resth1 ln2 resth2 rhs_b

(*
  - c_opt : coercion declaration
*)

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
  then (CF.mkFailCtx_in(Trivial_Reason (CF.mk_failure_must "no lemma found in both LHS and RHS nodes (do coercion)" 
      Globals.sl_error)), [])
  else begin 
    Debug.devel_zprint (lazy ("do_coercion: estate :" ^ (Cprinter.string_of_entail_state estate) ^ "\n")) pos;
    Debug.devel_zprint (lazy ("do_coercion: " ^ "c1 = " ^ c1 ^ ", c2 = " ^ c2 ^ "\n")) pos;
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
    if m==[] then  (CF.mkFailCtx_in(Trivial_Reason (CF.mk_failure_must 
        "cannot find matching node in antecedent (do coercion)" Globals.sl_error)), [])
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
  Debug.no_3 "apply_left_coercion" Cprinter.string_of_h_formula Cprinter.string_of_h_formula Cprinter.string_of_coercion pr
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
  (*left-coercion can be simple or complex*)
  if (coer.coercion_case = Cast.Simple) then
    (*simple lemmas with simple lhs with single node*)
    let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_br) = CF.extr_formula_base lhs_b in
    (*let _ = print_string("left coercion\n") in*)
    let f = mkBase resth1 lhs_p lhs_t lhs_fl lhs_br pos in
    let _ = Debug.devel_zprint (lazy ("apply_left_coercion: left_coercion:"
    ^ "\ n### c1 = " ^ c1
    ^ "\n ### anode = "^ (Cprinter.string_of_h_formula anode)
    ^ "\n")) pos in
    let ok, new_lhs = rewrite_coercion prog estate anode f coer lhs_b rhs_b rhs_b true pos in
    let _ = Debug.devel_zprint (lazy ( "apply_left_coercion: after rewrite_coercion"
    ^ "\n ### ok = "^ (string_of_int ok)
    ^ "\n ### new_lhs = "^ (Cprinter.string_of_formula new_lhs)
    ^ "\n\n")) pos in
    if ok>0 then begin
      (* lhs_b -> rhs_b *)
      (* anode |- _ *)
      (* unfold by removing LHS head anode, and replaced with rhs_b into new_lhs to continue *)
      let new_ctx1 = build_context ctx0 new_lhs pos in
	  (* let new_ctx = set_context_formula ctx0 new_lhs in *)
      let new_ctx = SuccCtx[((* set_context_must_match *) new_ctx1)] in
      let res, tmp_prf = heap_entail prog is_folding new_ctx conseq pos in
      let new_res =
        if ok == 1 then res
        else CF.invert_outcome res
      in
      let prf = mkCoercionLeft ctx0 conseq coer.coercion_head
	    coer.coercion_body tmp_prf coer.coercion_name
      in
	  (new_res, [prf])
    end else (CF.mkFailCtx_in( Basic_Reason ( { 
	    fc_message ="failed left coercion application";
	    fc_current_lhs = estate;
	    fc_prior_steps = estate.es_prior_steps;
	    fc_orig_conseq = estate.es_orig_conseq;
	    fc_current_conseq = CF.formula_of_heap HFalse pos; 
	    fc_failure_pts = match (get_node_label anode) with | Some s-> [s] | _ -> [];}, 
    CF.mk_failure_must "12" Globals.sl_error)), [])
  else
    (*COMPLEX or NORMALIZING lemmas with multiple nodes in the lhs*)
    (* (\*LDK: ok*\) *)
    (* let _ = print_string ("mmmm, heap_entail_non_empty_rhs_heap: " *)
    (* ^ "left_coercion: c1 = " *)
    (* ^ c1 ^ "\n") in *)
    let _ = Debug.devel_zprint (lazy ("heap_entail_non_empty_rhs_heap: "
    ^ "left_coercion: c1 = "
    ^ c1 ^ "\n")) pos in
    apply_left_coercion_complex  estate coer prog conseq ctx0 resth1 anode lhs_b rhs_b c1 is_folding pos



(*TOCHECK: use pickup node to pickup the self node*)
(*LDK: COMPLEX lemmas are treated in a different way*)
and apply_left_coercion_complex_x estate coer prog conseq ctx0 resth1 anode lhs_b rhs_b c1 is_folding pos =
  (*simple lemmas with simple lhs with single node*)
  let (lhs_h,lhs_p,lhs_t,lhs_fl,lhs_br) = CF.extr_formula_base lhs_b in
  (*let _ = print_string("left coercion\n") in*)
  let f = CF.mkBase resth1 lhs_p lhs_t lhs_fl lhs_br pos in
  let coer_lhs = coer.coercion_head in
  let coer_rhs = coer.coercion_body in
  (* let _ = print_string ("apply_left_coercion_complex_x: before rename" *)
  (*                       ^ "\n ### coer_lhs = " ^ (Cprinter.string_of_formula coer_lhs) *)
  (*                       ^ "\n ### coer_rhs = " ^ (Cprinter.string_of_formula coer_rhs) *)
  (*                       ^ "\n") in *)
  (************************************************************************)
  (* rename the free vars in the lhs and rhs to avoid name collision *)
  (* between lemmas and entailment formulas*)
  (* let lhs_fv = (fv_rhs coer_lhs coer_rhs) in *)
  let lhs_fv = (CF.fv coer_lhs) in
  let fresh_lhs_fv = CP.fresh_spec_vars lhs_fv in
  let tmp_rho = List.combine lhs_fv fresh_lhs_fv in
  let coer_lhs = CF.subst tmp_rho coer_lhs in
  let coer_rhs = CF.subst tmp_rho coer_rhs in
  (************************************************************************)
  (* let _ = print_string ("apply_left_coercion_complex_x : after rename" *)
  (*                       ^ "\n ### lhs_fv = " ^ (Cprinter.string_of_spec_var_list lhs_fv) *)
  (*                       ^ "\n ### coer_lhs = " ^ (Cprinter.string_of_formula coer_lhs) *)
  (*                       ^ "\n ### coer_rhs = " ^ (Cprinter.string_of_formula coer_rhs) *)
  (*                       ^ "\n") in *)
  let lhs_heap, lhs_guard, lhs_flow, lhs_branches, _ = split_components coer_lhs in
  (* let _ = print_string ("apply_left_coercion_complex_x:" *)
  (*                       ^ "\n ### f = " ^ (Cprinter.string_of_formula f) *)
  (*                       ^ "\n ### coer_lhs = " ^ (Cprinter.string_of_formula coer_lhs) *)
  (*                       ^ "\n ### coer_rhs = " ^ (Cprinter.string_of_formula coer_rhs) *)
  (*                       ^ "\n ### coer_guard = " ^ (Cprinter.string_of_mix_formula lhs_guard) *)
  (*                       ^ "\n") in *)
  let lhs_guard = MCP.fold_mem_lst (CP.mkTrue no_pos) false false (* true true *) lhs_guard in  (* TODO : check with_dupl, with_inv *)
  let lhs_hs = CF.split_star_conjunctions lhs_heap in (*|lhs_hs|>1*)
  let head_node, rest = pick_up_node lhs_hs Globals.self in
  let extra_opt = join_star_conjunctions_opt rest in
  let extra_heap = 
    (match (extra_opt) with
      | None -> 
            let _ = print_string "[normalize_perm] Warning: List of conjunctions can not be empty \n" in
            CF.HTrue
      | Some res_f -> res_f)
  in
  match anode, head_node with (*node -> current heap node | lhs_heap -> head of the coercion*)
    | ViewNode ({ h_formula_view_node = p1;
      h_formula_view_name = c1;
      h_formula_view_origins = origs;
      (* h_formula_view_original = original; (*LDK: unused*) *)
      h_formula_view_remaining_branches = br1;
      h_formula_view_perm = perm1; (*LDK*)
      h_formula_view_arguments = ps1} (* as h1 *)),
      ViewNode ({ h_formula_view_node = p2;
      h_formula_view_name = c2;
      h_formula_view_remaining_branches = br2;
      h_formula_view_perm = perm2; (*LDK*)
      h_formula_view_arguments = ps2} (* as h2 *)) 
	| DataNode ({ h_formula_data_node = p1;
	  h_formula_data_name = c1;
	  h_formula_data_origins = origs;
	  h_formula_data_remaining_branches = br1;
	  h_formula_data_perm = perm1; (*LDK*)
	  h_formula_data_arguments = ps1} (* as h1 *)),
      DataNode ({ h_formula_data_node = p2;
	  h_formula_data_name = c2;
	  h_formula_data_remaining_branches = br2;
	  h_formula_data_perm = perm2; (*LDK*)
	  h_formula_data_arguments = ps2} (* as h2 *)) when CF.is_eq_node_name(*is_eq_view_spec*) c1 c2 (*c1=c2 && (br_match br1 br2) *) ->

          (*temporarily skip this step. What is it for???*)
	      (* let apply_coer = (coer_target prog coer node (CF.formula_of_base target_b (\* rhs_b *\)) (CF.formula_of_base lhs_b)) in *)

          if (is_cycle_coer coer origs)
	      then
            (* let s = (pr_list string_of_bool [f1;(\* f2; *\)f3;f4;f5;f6]) in *)
		    let _ = Debug.devel_zprint (lazy("[apply_left_coercion_complex_x]:failed left coercion application: in a cycle!"(* ^s *))) pos in
            (CF.mkFailCtx_in( Basic_Reason ( { 
	            fc_message ="failed left coercion application: in a cycle";
	            fc_current_lhs = estate;
	            fc_prior_steps = estate.es_prior_steps;
	            fc_orig_conseq = estate.es_orig_conseq;
	            fc_current_conseq = CF.formula_of_heap HFalse pos; 
	            fc_failure_pts = match (get_node_label anode) with | Some s-> [s] | _ -> [];},
            CF.mk_failure_must "12" Globals.sl_error)), [])
          else
            let perms1,perms2 =
              if (Perm.allow_perm ()) then
                match perm1,perm2 with
                  | Some f1, Some f2 ->
                        ([f1],[f2])
                  | Some f1, None ->
                        ([f1],[full_perm_var])
                  | None, Some f2 ->
                        ([full_perm_var],[f2])
                  | None, None ->
                        ([],[])
              else
                ([],[])
            in
            let fr_vars = perms2@(p2 :: ps2)in
            let to_vars = perms1@(p1 :: ps1)in
            let lhs_guard_new = CP.subst_avoid_capture fr_vars to_vars lhs_guard in
		    let coer_rhs_new1 = subst_avoid_capture fr_vars to_vars coer_rhs in
            let extra_heap_new =  CF.subst_avoid_capture_h fr_vars to_vars extra_heap in
            let coer_rhs_new1,extra_heap_new =
              if (Perm.allow_perm ()) then
                match perm1,perm2 with
                  | Some f1, None ->
                        (*propagate perm into coercion*)
                        let rhs = propagate_perm_formula coer_rhs_new1 f1 in
                        let extra, svl =  propagate_perm_h_formula extra_heap_new f1 in
                        (rhs,extra)
                  | _ -> (coer_rhs_new1, extra_heap_new)
              else
                (coer_rhs_new1,extra_heap_new)
            in
		    let coer_rhs_new = add_origins coer_rhs_new1 (coer.coercion_name ::origs) in
            (*avoid apply a complex lemma twice*)
            let f = add_origins f [coer.coercion_name] in
            let f = add_original f false in
            let new_es_heap = CF.mkStarH anode estate.es_heap no_pos in (*consumed*)
            (* let new_es_heap = CF.mkStarH head_node estate.es_heap no_pos in *)
            let old_trace = estate.es_trace in
            let new_estate = {estate with es_heap = new_es_heap; es_formula = f;es_trace=("(Complex)"::old_trace)} in
            let new_ctx1 = Ctx new_estate in
            let new_ctx = SuccCtx[((* set_context_must_match *) new_ctx1)] in
            (*prove extra heap + guard*)
            let conseq_extra = mkBase extra_heap_new (MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) lhs_guard_new) CF.TypeTrue (CF.mkTrueFlow ()) [] pos in 
            (* let conseq_extra = mkBase extra_heap_new (MCP.OnePF (CP.mkTrue no_pos)) CF.TypeTrue (CF.mkTrueFlow ()) [] pos in *)           
	        Debug.devel_zprint (lazy ("apply_left_coercion_complex: check extra heap")) pos;
	        Debug.devel_zprint (lazy ("apply_left_coercion_complex: new_ctx after folding: "
		    ^ (Cprinter.string_of_spec_var p2) ^ "\n"
		    ^ (Cprinter.string_of_context new_ctx1))) pos;
	        Debug.devel_zprint (lazy ("apply_left_coercion_complex: conseq_extra:\n"
		    ^ (Cprinter.string_of_formula conseq_extra))) pos;

            let check_res, check_prf = heap_entail prog false new_ctx conseq_extra pos in

	        Debug.devel_zprint (lazy ("apply_left_coercion_complex: after check extra heap: "
		    ^ (Cprinter.string_of_spec_var p2) ^ "\n"
		    ^ (Cprinter.string_of_list_context check_res))) pos;

            (*PROCCESS RESULT*)
            let rec process_one_x (ss:CF.steps) res = match res with
              | OCtx (c1, c2) ->
	                let tmp1, prf1 = process_one_x (add_to_steps ss "left OR 4 in ante") c1 in
	                let tmp2, prf2 = process_one_x  (add_to_steps ss "right OR 4 in ante") c2 in
	                let tmp3 = or_list_context tmp1 tmp2 in
	                let prf3 = Prooftracer.mkOrLeft res f [prf1; prf2] in
	                (tmp3, prf3)
              | Ctx es ->
                    let es = CF.overwrite_estate_with_steps es ss in
                    (* rhs_coerc * es.es_formula /\ lhs.p |-  conseq*)
                    (* let es_formula = es.es_formula in *)
                    (* let es_formula_heap,_,es_flow,es_branches, _ = split_components es_formula in *)
                    (* let new_es_f = mkBase es_formula_heap (MCP.OnePF (CP.mkTrue no_pos)) CF.TypeTrue es_flow es_branches pos in *)
                    (* let new_ante1 = normalize_combine coer_rhs_new new_es_f no_pos in *)

                    let new_ante1 = normalize_combine coer_rhs_new es.es_formula no_pos in
                    let new_ante = add_mix_formula_to_formula lhs_p new_ante1 in
                    let new_es = {new_estate with es_formula=new_ante; es_trace=old_trace} in
                    let new_ctx = (Ctx new_es) in

	                Debug.devel_zprint (lazy ("apply_left_coercion_complex: process_one: resume entail check")) pos;
	                Debug.devel_zprint (lazy ("apply_left_coercion_complex: process_one: resume entail check: new_ctx = \n" ^ (Cprinter.string_of_context new_ctx))) pos;
	                Debug.devel_zprint (lazy ("apply_left_coercion_complex: process_one: resume entail check: conseq = " ^ (Cprinter.string_of_formula conseq))) pos;


	                let rest_rs, prf = heap_entail_one_context prog is_folding new_ctx conseq pos in


	                Debug.devel_zprint (lazy ("apply_left_coercion_complex: process_one: after resume entail check: rest_res =  " ^ (Cprinter.string_of_list_context check_res))) pos;

                    (rest_rs,prf)
            in
            let process_one (ss:CF.steps) res = 
              let pr1 = Cprinter.string_of_context  in
              let pr2 (c,_) = Cprinter.string_of_list_context c in
              Debug.no_1 "apply_left_coercion_complex: process_one" pr1 pr2 (fun _ -> process_one_x (ss:CF.steps) res) res in

            (match check_res with 
              | FailCtx _ -> 
                    let _ = Debug.devel_zprint (lazy ("apply_left_coercion_complex: extra state of the lhs is not satisfied \n")) pos in
                    (CF.mkFailCtx_in( Basic_Reason ( { 
	                    fc_message ="failed left coercion application: can not match extra heap";
	                    fc_current_lhs = estate;
	                    fc_prior_steps = estate.es_prior_steps;
	                    fc_orig_conseq = estate.es_orig_conseq;
	                    fc_current_conseq = CF.formula_of_heap HFalse pos; 
	                    fc_failure_pts = match (get_node_label anode) with | Some s-> [s] | _ -> [];},
                    CF.mk_failure_must "12" Globals.sl_error)), [])
              | SuccCtx res -> 
	                let t1,p1 = List.split (List.map (process_one []) res) in
	                let t1 = fold_context_left t1 in
	                (t1,p1))
    | _ -> 
          (CF.mkFailCtx_in( Basic_Reason ( { 
	          fc_message ="failed left coercion application, can not match head node";
	          fc_current_lhs = estate;
	          fc_prior_steps = estate.es_prior_steps;
	          fc_orig_conseq = estate.es_orig_conseq;
	          fc_current_conseq = CF.formula_of_heap HFalse pos; 
	          fc_failure_pts = match (get_node_label anode) with | Some s-> [s] | _ -> [];},
          CF.mk_failure_must "12" Globals.sl_error)), [])

and apply_left_coercion_complex estate coer prog conseq ctx0 resth1 anode lhs_b rhs_b c1 is_folding pos=
  let pr (e,_) = Cprinter.string_of_list_context e in
  Debug.no_3 "apply_left_coercion_complex" Cprinter.string_of_h_formula Cprinter.string_of_h_formula Cprinter.string_of_coercion pr
      (fun _ _ _ -> apply_left_coercion_complex_x estate coer prog conseq ctx0 resth1 anode lhs_b rhs_b c1 is_folding pos) anode resth1 coer

(*pickup a node named "name" from a list of nodes*)
and pick_up_node_x (ls:CF.h_formula list) (name:ident):(CF.h_formula * CF.h_formula list) =
  let rec helper ls =
    match ls with
      | [] -> CF.HTrue,[]
      | x::xs ->
            match x with
              | ViewNode ({h_formula_view_node = c})
              | DataNode ({h_formula_data_node = c}) ->

                    let c_str = (CP.name_of_spec_var c) in
                    let ri = try  (String.rindex c_str '_') with  _ -> (String.length c_str) in
                    let c_name = (String.sub c_str 0 ri)  in
                    (* let _ = print_string ("pick_up_node:" ^ c_name ^ " &&"  ^ name ^ "\n\n " ) in *)
                    if ((String.compare c_name name) ==0)
                    then
                      (x,xs)
                    else
                      let res1,res2 = helper xs in
                      (res1,x::res2)
              | _ ->
                    let res1,res2 = helper xs in
                    (res1,x::res2)
  in helper ls

(*pickup a node named "name" from a list of nodes*)
and pick_up_node (ls:CF.h_formula list) (name:ident):(CF.h_formula * CF.h_formula list) =
  let rec pr xs = 
    match xs with
      | [] -> ""
      | x::xs1 -> (!print_h_formula x) ^ "|*|" ^ pr xs1
  in
  let pr2 (a,b) =
    (Cprinter.string_of_h_formula a) ^ "|&&&|"  ^ (pr b)
  in
  Debug.no_2 "pick_up_node"
      pr (fun id -> id) pr2
      pick_up_node_x ls name

(*normalize a formula using normalization lemma*)
(*normaliztion lemmas are similar to complex lemma*)
(*However, they reduce the number of nodes after each application*)
(*while complex lemmas can be arbitary*)

and normalize_w_coers prog (estate:CF.entail_state) (coers:coercion_decl list) (h:h_formula) (p:MCP.mix_formula) : (h_formula * MCP.mix_formula) =
  let rec helper (estate:CF.entail_state) (h:h_formula) (p:MCP.mix_formula) : (h_formula*MCP.mix_formula) =
    (*try to check whether the current estate with h=anode*rest and pure=p 
      can entail the lhs of an coercion*)
    let process_one_x estate anode rest coer h p =
      let f = mkBase rest p CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in
      let coer_lhs = coer.coercion_head in
      let coer_rhs = coer.coercion_body in

      (*compute free vars in extra heap and guard*)
      let compute_extra_vars () =
        let lhs_heap, lhs_guard, _, _, _ = split_components coer_lhs in
        let lhs_hs = CF.split_star_conjunctions lhs_heap in (*|lhs_hs|>1*)
        let head_node, rest = pick_up_node lhs_hs Globals.self in
        (* let head_node = List.hd lhs_hs in *)
        (* let extra_opt = join_star_conjunctions_opt (List.tl lhs_hs) in *)
        let extra_opt = join_star_conjunctions_opt rest in
        let extra_heap =
          (match (extra_opt) with
            | None ->
                  let _ = print_string "[normalize_perm] Warning: List of conjunctions can not be empty \n" in
                  CF.HTrue
            | Some res_f -> res_f)
        in
        let h_vars = CF.h_fv head_node in
        let e_vars = CF.h_fv extra_heap in
        let p_vars = MCP.mfv lhs_guard in
        let vars = Gen.BList.difference_eq CP.eq_spec_var (e_vars@p_vars) h_vars in
        Gen.BList.remove_dups_eq CP.eq_spec_var vars
      in
      (* rename the bound vars *)
      let extra_vars = compute_extra_vars () in
      let extra_vars_new =  CP.fresh_spec_vars extra_vars in
      let tmp_rho = List.combine extra_vars extra_vars_new in
      let coer_lhs = CF.subst tmp_rho coer_lhs in
      let coer_rhs = CF.subst tmp_rho coer_rhs in
      (************************************************************************)
      (* also rename the free vars from the rhs that do not appear in the lhs *)
      let lhs_fv = (fv_rhs coer_lhs coer_rhs) in
      let fresh_lhs_fv = CP.fresh_spec_vars lhs_fv in
      let tmp_rho = List.combine lhs_fv fresh_lhs_fv in
      let coer_lhs = CF.subst tmp_rho coer_lhs in
      let coer_rhs = CF.subst tmp_rho coer_rhs in
      (************************************************************************)
      (* (\************************************************************************\) *)
      (* (\* rename the free vars in the lhs and rhs to avoid name collision *\) *)
      (* (\* between lemmas and entailment formulas*\) *)
      (* (\* let lhs_fv = (fv_rhs coer_lhs coer_rhs) in *\) *)
      (* let lhs_fv = (CF.fv coer_lhs) in *)
      (* let fresh_lhs_fv = CP.fresh_spec_vars lhs_fv in *)
      (* let tmp_rho = List.combine lhs_fv fresh_lhs_fv in *)
      (* let coer_lhs = CF.subst tmp_rho coer_lhs in *)
      (* let coer_rhs = CF.subst tmp_rho coer_rhs in *)
      (* (\************************************************************************\) *)
      (* let _ = print_string ("normalize_w_coers: before and after renamed" *)
      (*                       ^ "\n ### coer.coercion_head = " ^ (Cprinter.string_of_formula coer.coercion_head) *)
      (*                       ^ "\n ### coer.coercion_body = " ^ (Cprinter.string_of_formula coer.coercion_body) *)
      (*                       ^ "\n ### coer_lhs = " ^ (Cprinter.string_of_formula coer_lhs) *)
      (*                       ^ "\n ### coer_rhs = " ^ (Cprinter.string_of_formula coer_rhs) *)
      (*                       ^ "\n") in *)

      let lhs_heap, lhs_guard, lhs_flow, lhs_branches, _ = split_components coer_lhs in
      let lhs_guard = MCP.fold_mem_lst (CP.mkTrue no_pos) false false (* true true *) lhs_guard in  (* TODO : check with_dupl, with_inv *)
      let lhs_hs = CF.split_star_conjunctions lhs_heap in (*|lhs_hs|>1*)
      (* let lhs_hs = List.rev lhs_hs in *)
      let head_node, rest = pick_up_node lhs_hs Globals.self in
      (* let head_node = List.hd lhs_hs in *)
      (* let extra_opt = join_star_conjunctions_opt (List.tl lhs_hs) in *)
      let extra_opt = join_star_conjunctions_opt rest in
      let extra_heap =
        (match (extra_opt) with
          | None ->
                let _ = print_string "[normalize_perm] Warning: List of conjunctions can not be empty \n" in
                CF.HTrue
          | Some res_f -> res_f)
      in
      (* let _ = print_string ("normalize_w_coers: before and after renamed" *)
      (*                       ^ "\n ### lhs_heap = " ^ (Cprinter.string_of_h_formula lhs_heap) *)
      (*                       ^ "\n ### head_node = " ^ (Cprinter.string_of_h_formula head_node) *)
      (*                       ^ "\n ### anode = " ^ (Cprinter.string_of_h_formula anode) *)

      (*                       ^ "\n") in *)
      match anode, head_node with (*node -> current heap node | lhs_heap -> head of the coercion*)
        | ViewNode ({ h_formula_view_node = p1;
          h_formula_view_name = c1;
          h_formula_view_origins = origs;
          (* h_formula_view_original = original; (*LDK: unused*) *)
          h_formula_view_remaining_branches = br1;
          h_formula_view_perm = perm1; (*LDK*)
          h_formula_view_arguments = ps1} (* as h1 *)),
          ViewNode ({ h_formula_view_node = p2;
          h_formula_view_name = c2;
          h_formula_view_remaining_branches = br2;
          h_formula_view_perm = perm2; (*LDK*)
          h_formula_view_arguments = ps2} (* as h2 *))
	    | DataNode ({ h_formula_data_node = p1;
	      h_formula_data_name = c1;
	      h_formula_data_origins = origs;
	      h_formula_data_remaining_branches = br1;
	      h_formula_data_perm = perm1; (*LDK*)
	      h_formula_data_arguments = ps1} (* as h1 *)),
          DataNode ({ h_formula_data_node = p2;
	      h_formula_data_name = c2;
	      h_formula_data_remaining_branches = br2;
	      h_formula_data_perm = perm2; (*LDK*)
	      h_formula_data_arguments = ps2} (* as h2 *)) when CF.is_eq_node_name(*is_eq_view_spec*) c1 c2 (*c1=c2 && (br_match br1 br2) *) ->

              let perms1,perms2 =
                if (Perm.allow_perm ()) then
                  match perm1,perm2 with
                    | Some f1, Some f2 ->
                          ([f1],[f2])
                    | Some f1, None ->
                          ([f1],[full_perm_var])
                    | None, Some f2 ->
                          ([full_perm_var],[f2])
                    | None, None ->
                          ([],[])
                else
                  ([],[])
              in
              let fr_vars = perms2@(p2 :: ps2)in
              let to_vars = perms1@(p1 :: ps1)in
              let lhs_guard_new = CP.subst_avoid_capture fr_vars to_vars lhs_guard in
		      let coer_rhs_new1 = subst_avoid_capture fr_vars to_vars coer_rhs in
              let extra_heap_new =  CF.subst_avoid_capture_h fr_vars to_vars extra_heap in
              let coer_rhs_new1,extra_heap_new =
                if (Perm.allow_perm ()) then
                  match perm1,perm2 with
                    | Some f1, None ->
                          (*propagate perm into coercion*)
                          let rhs = propagate_perm_formula coer_rhs_new1 f1 in
                          let extra, svl =  propagate_perm_h_formula extra_heap_new f1 in
                          (rhs,extra)
                    | _ -> (coer_rhs_new1, extra_heap_new)
                else
                  (coer_rhs_new1,extra_heap_new)
              in
		      let coer_rhs_new = add_origins coer_rhs_new1 ((* coer.coercion_name :: *)origs) in
              let new_es_heap = anode in (*consumed*)
              let old_trace = estate.es_trace in
              let new_estate = {estate with es_heap = new_es_heap; es_formula = f;es_trace=("(normalizing)"::old_trace); es_is_normalizing = true} in
              let new_ctx1 = Ctx new_estate in
              let new_ctx = SuccCtx[((* set_context_must_match *) new_ctx1)] in
              (*prove extra heap + guard*)
              let conseq_extra = mkBase extra_heap_new (MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) lhs_guard_new) CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in 
              (* let conseq_extra = mkBase extra_heap_new (MCP.OnePF (CP.mkTrue no_pos)) CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in  *)

	          Debug.devel_zprint (lazy ("normalize_w_coers:process_one: check extra heap")) no_pos;
	          Debug.devel_zprint (lazy ("normalize_w_coers:process_one: new_ctx: "
		      ^ (Cprinter.string_of_spec_var p2) ^ "\n"
		      ^ (Cprinter.string_of_context new_ctx1))) no_pos;
	          Debug.devel_zprint (lazy ("normalize_w_coers:process_one: conseq_extra:\n"
		      ^ (Cprinter.string_of_formula conseq_extra))) no_pos;

              let check_res, check_prf = heap_entail prog false new_ctx conseq_extra no_pos in

	          Debug.devel_zprint (lazy ("normalize_w_coers:process_one: after check extra heap: "
		      ^ (Cprinter.string_of_spec_var p2) ^ "\n"
		      ^ (Cprinter.string_of_list_context check_res))) no_pos;

              (*PROCCESS RESULT*)
              match check_res with 
                | FailCtx _ -> 
                      (*false, return dummy h and p*)
                      (false, estate, h,p)
                | SuccCtx res -> 
                      (*we expect only one result*)
                      let ctx = List.hd res in
                      match ctx with
                        | OCtx (c1, c2) ->
                              let _ = print_string ("[solver.ml] Warning: normalize_w_coers:process_one: expect only one context \n") in
                              (false,estate,h,p)
                        | Ctx es ->
                              let new_ante1 = normalize_combine coer_rhs_new es.es_formula no_pos in
                              let new_ante = add_mix_formula_to_formula p new_ante1 in
                              let new_ante = CF.remove_dupl_conj_eq_formula new_ante in
                              let h1,p1,_,_,_ = split_components new_ante in
                              let new_es = {new_estate with es_formula=new_ante; es_trace=old_trace} in
                              (true,new_es,h1,p1)
    in
    let process_one estate anode rest coer h p =
      let pr (c1,c2,c3,c4) = string_of_bool c1 ^ "||" ^ Cprinter.string_of_entail_state c2 in 
      Debug.no_5 "process_one" Cprinter.string_of_entail_state Cprinter.string_of_h_formula Cprinter.string_of_h_formula Cprinter.string_of_h_formula  Cprinter.string_of_mix_formula pr  
          (fun _ _ _ _ _ -> process_one_x estate anode rest coer h p) estate anode rest  h p 
    in
    (*process a list of pairs (anode * rest) *)
    let rec process_one_h h_lst =
      match h_lst with
        | [] -> 
              (*so far, could not find any entailment -> can not normalize*)
              h,p
        | (anode,rest)::xs ->
              (*for each pair (anode,rest), find a list of coercions*)
              let name = match anode with
                | ViewNode vn -> vn.h_formula_view_name
                | DataNode dn -> dn.h_formula_data_name
                | _ -> 
                      let _ = print_string("[solver.ml] Warning: normalize_w_coers expecting DataNode or ViewNode \n") in
                      ""
              in
              let c_lst = look_up_coercion_def_raw coers name in (*list of coercions*)
              let lst = List.map (fun c -> (c,anode,rest)) c_lst in
              (*process a triple (coer,anode,res)*)
              let rec process_one_coerc lst =
                match lst with
                  | [] -> 
                        (*so far, there is no entailment -> process the rest of pairs of (anode,rest)*)
                        process_one_h xs 
                  | ((coer,anode,res)::xs1) ->
                        (*for each triple, try to find a posible entailment*)
                        let res,res_es,res_h,res_p = process_one estate anode rest coer h p in
                        if (res) (*we could find a result*)
                        then
                          (*restart and normalize the new estate*)
                          helper res_es res_h res_p
                        else
                          (*otherwise, try the rest*)
                          process_one_coerc xs1
              in
              process_one_coerc lst
    in
    (*split into pairs of (single node * the rest)  *)
    let h_lst = split_linear_node_guided [] h in
    process_one_h h_lst
  in
  helper estate h p (*start*)

and normalize_formula_w_coers_x prog estate (f:formula) (coers:coercion_decl list): formula =
  if (isAnyConstFalse f) then f
  else
    let coers = List.filter (fun c -> 
        match c.coercion_case with
          | Cast.Simple -> false
          | Cast.Complex -> false
          | Cast.Normalize -> true) coers
    in
    (* let _ = print_string ("normalize_formula_w_coers: "  *)
    (*                       ^ " ### coers = " ^ (Cprinter.string_of_coerc_list coers) *)
    (*                       ^ "\n\n") *)
    (* in *)
    let rec helper f =
      match f with
        | Base b ->
              let h = b.formula_base_heap in
              let p = b.formula_base_pure in
              (* let t = b.formula_base_type in *)
              (* let fl = b.formula_base_flow in *)
              (* let br = b.formula_base_branches in *)
              let h,p = normalize_w_coers prog estate coers h p (* t fl br *) in
              Base {b with formula_base_heap=h;formula_base_pure=p}
        | Exists e ->
              let h = e.formula_exists_heap in
              let p = e.formula_exists_pure in
              (* let t = e.formula_exists_type in *)
              (* let fl = e.formula_exists_flow in *)
              (* let br = e.formula_exists_branches in *)
              let h,p = normalize_w_coers prog estate coers h p (* t fl br *) in
              Exists {e with formula_exists_heap=h; formula_exists_pure=p }
        | Or o ->
	          let f1 = helper o.formula_or_f1 in
	          let f2 = helper o.formula_or_f2 in
              Or {o with formula_or_f1 = f1; formula_or_f2 = f2}
    in helper f

and normalize_formula_w_coers prog estate (f:formula) (coers:coercion_decl list): formula =
  Debug.no_1 "normalize_formula_w_coers" Cprinter.string_of_formula Cprinter.string_of_formula
      (fun _ -> normalize_formula_w_coers_x  prog estate f coers) f
      
(*******************************************************************************************************************************************************************************************)
(* apply_right_coercion *)
(*******************************************************************************************************************************************************************************************)
and apply_right_coercion estate coer prog (conseq:CF.formula) ctx0 resth2 ln2 (*rhs_p rhs_t rhs_fl*) lhs_b rhs_b (c2:ident) is_folding pos =
  let pr (e,_) = Cprinter.string_of_list_context e in
  Debug.no_4 "apply_right_coercion" Cprinter.string_of_h_formula Cprinter.string_of_h_formula Cprinter.string_of_coercion
      Cprinter.string_of_formula_base
      (* Cprinter.string_of_formula (fun x -> x)  *)pr
      (fun _ _ _ _ -> apply_right_coercion_a estate coer prog (conseq:CF.formula) ctx0 resth2 ln2 (*rhs_p rhs_t rhs_fl*) lhs_b rhs_b (c2:ident) is_folding pos) ln2 resth2 coer  rhs_b (* conseq c2 *)

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
  let (_,rhs_p,rhs_t,rhs_fl,rhs_br) = CF.extr_formula_base rhs_b in
  (*let _ = print_string("right coercion\n") in*)
  let f = mkBase resth2 rhs_p rhs_t rhs_fl [] pos in
  let _ = Debug.devel_zprint (lazy ("do_right_coercion : c2 = "
  ^ c2 ^ "\n")) pos in
  (* if is_coercible ln2 then *)
  let ok, new_rhs = rewrite_coercion prog estate ln2 f coer lhs_b rhs_b lhs_b false pos in
  if (is_coercible ln2)&& (ok>0)  then begin
    (* lhs_b <- rhs_b *)
    (*  _ |- ln2 *)
    (*  fold by removing a single RHS node ln2, and replaced with lhs_b into new_rhs with explicit instantiations *)
    (* need to make implicit var become explicit *)
    let vl = Gen.BList.intersect_eq CP.eq_spec_var estate.es_gen_impl_vars (h_fv ln2) in
    let new_iv = Gen.BList.difference_eq CP.eq_spec_var estate.es_gen_impl_vars vl in
    let _ = if not(vl==[]) then Debug.devel_zprint (lazy ("do_right_coercion : impl to expl vars  " ^ (Cprinter.string_of_spec_var_list vl) ^ "\n")) pos in
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
    let _ = Debug.devel_zprint (lazy ("do_right_coercion :  " ^ c2 ^ "failed \n")) pos in
    (CF.mkFailCtx_in(Basic_Reason ( {fc_message ="failed right coercion application";
    fc_current_lhs = estate;
    fc_prior_steps = estate.es_prior_steps;
    fc_orig_conseq = estate.es_orig_conseq;
    fc_current_conseq = CF.formula_of_heap HFalse pos;
    fc_failure_pts = match (get_node_label ln2) with | Some s-> [s] | _ -> [];},
    CF.mk_failure_must "13" Globals.sl_error)), [])
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
  let f, flag = elim_exists_exp_loop f0 in
  if flag then (elim_exists_exp f)
  else f 

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
	        let tmp = mkBase h pp1 t fl b pos in
		    (*let _ = (print_string (" Base formula: " ^ (Cprinter.string_of_formula tmp) ^ "\n")) in*)
	        let new_baref = subst_exp [one_subst] tmp in
 		    (*let _ = (print_string (" new_baref: " ^ (Cprinter.string_of_formula new_baref) ^ "\n")) in*)
	        let tmp2 = add_quantifiers rest_qvars new_baref in
	        let tmp3, _ = elim_exists_exp_loop tmp2 in
		    (tmp3, true)
	      else (* if qvar is not equated to any variables, try the next one *)
	        let tmp1 = mkExists rest_qvars h p t fl b pos in
	        let tmp2, flag = elim_exists_exp_loop tmp1 in
	        let tmp3 = add_quantifiers [qvar] tmp2 in
		    (tmp3, flag)
	    else (* anyway it's going to stay in the heap part so we can't eliminate --> try eliminate the rest of them, and then add it back to the exist quantified vars *)
	      let tmp1 = mkExists rest_qvars h p t fl b pos in
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
		(*| EVariance e -> ECase {b with formula_case_branches =  (List.map (fun (c1,c2) -> 
          (c1,(combine_struc [f2] c2))) b.formula_case_branches)} *)
        | EInfer _ -> ECase {b with formula_case_branches =  (List.map (fun (c1,c2)-> (c1,(combine_struc [f2] c2))) b.formula_case_branches)}
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
		(*| EVariance _ -> EBase ({b with formula_ext_continuation = combine_struc b.formula_ext_continuation [f2]})*)
        | EInfer _ -> EBase ({b with formula_ext_continuation = combine_struc b.formula_ext_continuation [f2]})
	  in r
    | EAssume (x1,b, (y1',y2') )-> let r = match f2 with
	    | ECase d -> combine_ext_struc f2 f1
	    | EBase d -> combine_ext_struc f2 f1 
	    | EAssume (x2,d,(y1,y2)) -> EAssume ((x1@x2),(normalize_combine b d (Cformula.pos_of_formula d)),(y1,(y2^y2')))
		(*| EVariance e -> combine_ext_struc f2 f1*)
        | EInfer _ -> combine_ext_struc f2 f1
	  in r
	(*| EVariance e -> let r = match f2 with
		| ECase c -> ECase {c with formula_case_branches =  (List.map (fun (c1,c2)-> (c1,(combine_struc [f1] c2))) c.formula_case_branches)}
		| EBase _ -> EVariance ({e with formula_var_continuation = combine_ext_struc e.formula_var_continuation f2})
		| EAssume _ -> EVariance ({e with formula_var_continuation = combine_ext_struc e.formula_var_continuation f2})
    | EInfer _ -> EVariance ({e with formula_var_continuation = combine_ext_struc e.formula_var_continuation f2})
		| EVariance e2 -> EVariance ({e with 
        formula_var_measures = e.formula_var_measures @ e2.formula_var_measures;
			  formula_var_infer = e.formula_var_infer @ e2.formula_var_infer; 
			  formula_var_continuation = combine_ext_struc e.formula_var_continuation e2.formula_var_continuation}) 
	  in r*)
    | EInfer e -> let r = match f2 with
        | ECase c -> ECase {c with formula_case_branches =  (List.map (fun (c1,c2)-> (c1,(combine_struc [f1] c2))) c.formula_case_branches)}
        | EBase _ -> EInfer ({e with formula_inf_continuation = combine_ext_struc e.formula_inf_continuation f2})
        | EAssume _ -> EInfer ({e with formula_inf_continuation = combine_ext_struc e.formula_inf_continuation f2})
        (*| EVariance _ -> EInfer ({e with formula_inf_continuation = combine_ext_struc e.formula_inf_continuation f2})*)
        | EInfer e2 -> EInfer ({e with formula_inf_vars = e.formula_inf_vars @ e2.formula_inf_vars;
              formula_inf_continuation = combine_ext_struc e.formula_inf_continuation e2.formula_inf_continuation}) 
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
      
and transform_null (eqs) :(CP.b_formula list) = List.map (fun c ->
    let (pf,il) = c in
    match pf with
      | Cpure.BVar _ 
      | Cpure.Lt _
      | Cpure.Lte _ -> c
      | Cpure.Eq (e1,e2,l) -> 
		    if (Cpure.exp_is_object_var e1)&&(Cpure.is_num e2) then
		      if (Cpure.is_zero_int e2) then (Cpure.Eq (e1,(Cpure.Null l),l), il)
		      else (Cpure.Neq (e1,(Cpure.Null l),l), il)
		    else if (Cpure.exp_is_object_var e2)&&(Cpure.is_num e1) then
		      if (Cpure.is_zero_int e1) then (Cpure.Eq (e2,(Cpure.Null l),l), il)
		      else (Cpure.Neq (e2,(Cpure.Null l),l), il)
		    else c
      | Cpure.Neq (e1,e2,l)-> 
		    if (Cpure.exp_is_object_var e1)&&(Cpure.is_num e2) then
		      if (Cpure.is_zero_int e2) then (Cpure.Neq (e1,(Cpure.Null l),l), il)
		      else c
		    else if (Cpure.exp_is_object_var e2)&&(Cpure.is_num e1) then
		      if (Cpure.is_zero_int e1) then (Cpure.Neq (e2,(Cpure.Null l),l), il)
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
  Debug.devel_zprint (lazy ("heap_entail_init struc_list_partial_context_init:"
          ^ "\nconseq:"^ (Cprinter.string_of_struc_formula conseq) 
         ^ "\nctx:\n" ^ (Cprinter.string_of_list_partial_context cl)
  ^"\n")) pos; 
  Gen.Profiling.push_time "entail_prune";
  let cl = prune_ctx_list prog cl in
(*  let _ = count_br_specialized prog cl in*)
  let conseq = prune_pred_struc prog false conseq in
  Gen.Profiling.pop_time "entail_prune";
  heap_entail_prefix_init prog is_folding  has_post cl conseq pos pid (rename_labels_struc,Cprinter.string_of_struc_formula,(heap_entail_one_context_struc_nth "1"))

let heap_entail_struc_list_failesc_context_init (prog : prog_decl) (is_folding : bool)  (has_post: bool)
	(cl : list_failesc_context) (conseq:struc_formula) pos (pid:control_path_id) : (list_failesc_context * proof) = 
  let _ = set_entail_pos pos in
  Debug.devel_zprint (lazy ("heap_entail_init struc_list_failesc_context_init:"
          ^ "\nconseq:"^ (Cprinter.string_of_struc_formula conseq) 
         ^ "\nctx:\n" ^ (Cprinter.string_of_list_failesc_context cl)
  ^"\n")) pos; 
  let res,prf = heap_entail_failesc_prefix_init 1 prog is_folding  has_post cl conseq pos pid (rename_labels_struc,Cprinter.string_of_struc_formula,(heap_entail_one_context_struc_nth "2")) in
  (CF.list_failesc_context_simplify res,prf)

let heap_entail_struc_list_failesc_context_init (prog : prog_decl) (is_folding : bool)  (has_post: bool)
	(cl : list_failesc_context) (conseq:struc_formula) pos (pid:control_path_id) : (list_failesc_context * proof) =
  Debug.no_2 "heap_entail_struc_list_failesc_context_init"
	Cprinter.string_of_list_failesc_context
	Cprinter.string_of_struc_formula
	(fun (cl, _) -> Cprinter.string_of_list_failesc_context cl)
	(fun _ _ -> heap_entail_struc_list_failesc_context_init prog is_folding has_post cl conseq pos pid) cl conseq

let heap_entail_list_partial_context_init (prog : prog_decl) (is_folding : bool)  (cl : list_partial_context)
        (conseq:formula) pos (pid:control_path_id) : (list_partial_context * proof) = 
  let _ = set_entail_pos pos in
  Debug.devel_zprint (lazy ("heap_entail_init list_partial_context_init:"
          ^ "\nconseq:"^ (Cprinter.string_of_formula conseq) 
        ^ "\nctx:\n" ^ (Cprinter.string_of_list_partial_context cl)
  ^"\n")) pos; 
  Gen.Profiling.push_time "entail_prune";  
  if cl==[] then ([],UnsatAnte)
  else begin
  let cl = reset_original_list_partial_context cl in
  let cl_after_prune = prune_ctx_list prog cl in
  let conseq = prune_preds prog false conseq in
  Gen.Profiling.pop_time "entail_prune";
  let entail_fct = (fun c-> heap_entail_prefix_init prog is_folding  false c 
      conseq pos pid (rename_labels_formula ,Cprinter.string_of_formula,heap_entail_one_context_new)) in
  heap_entail_agressive_prunning entail_fct (prune_ctx_list prog) (fun (c,_)-> isSuccessListPartialCtx_new c) cl_after_prune 
  end

let heap_entail_list_partial_context_init (prog : prog_decl) (is_folding : bool)  (cl : list_partial_context)
        (conseq:formula) pos (pid:control_path_id) : (list_partial_context * proof) = 
  (*let pr x = (string_of_int(List.length x))^"length" in*)
  let pr2 = Cprinter.string_of_list_partial_context in 
  Debug.no_2 (* loop_2_no *) "heap_entail_list_partial_context_init" pr2 (Cprinter.string_of_formula) 
      (fun (x,_) -> pr2 x)
      (fun _ _ -> heap_entail_list_partial_context_init prog is_folding  cl conseq pos pid) cl conseq

let heap_entail_list_failesc_context_init (prog : prog_decl) (is_folding : bool)  (cl : list_failesc_context)
      (conseq:formula) pos (pid:control_path_id) : (list_failesc_context * proof) =
  let _ = set_entail_pos pos in
  Debug.devel_zprint (lazy ("heap_entail_init list_failesc_context_init:"
  ^ "\nconseq:"^ (Cprinter.string_of_formula conseq) 
  ^ "\nctx:\n" ^ (Cprinter.string_of_list_failesc_context cl)
  ^"\n")) pos;
  if cl==[] then ([],UnsatAnte)
  else begin 
    Gen.Profiling.push_time "entail_prune";  
    let cl_after_prune = prune_ctx_failesc_list prog cl in
    let conseq = prune_preds prog false conseq in
    Gen.Profiling.pop_time "entail_prune";
    let (lfc,prf) = heap_entail_failesc_prefix_init 2 prog is_folding  false cl_after_prune conseq pos pid (rename_labels_formula ,Cprinter.string_of_formula,heap_entail_one_context_new) in
    (CF.convert_must_failure_4_list_failesc_context "failed proof @ loc" lfc,prf)
  end

let heap_entail_list_failesc_context_init (prog : prog_decl) (is_folding : bool)  (cl : list_failesc_context)
      (conseq:formula) pos (pid:control_path_id) : (list_failesc_context * proof) =
  let pr2 = Cprinter.string_of_formula in
  let pr1 = Cprinter.string_of_list_failesc_context in
  Debug.no_2 "heap_entail_list_failesc_context_init" 
      pr1 pr2 (fun (r,_)->pr1 r)
      (fun _ _ -> heap_entail_list_failesc_context_init prog is_folding cl conseq pos pid) cl conseq

(* TODO : what is this verify_pre_is_sat verification for? *)
let rec verify_pre_is_sat prog fml = match fml with
  | Or _ -> report_error no_pos "Do not expect disjunction in precondition"
  | Base b -> 
        let fml,_,_,_ = xpure prog fml 
        in TP.is_sat_raw (MCP.pure_of_mix fml)
  | Exists e ->
    let fml = normalize_combine_heap 
      (formula_of_mix_formula e.formula_exists_pure no_pos) e.formula_exists_heap
    in verify_pre_is_sat prog fml

let verify_pre_is_sat prog fml = 
  let pr = Cprinter.string_of_formula in
  Debug.no_1 "verify_pre_is_sat" pr pr_no 
      (fun _ -> verify_pre_is_sat prog fml) fml

(*let rec simplify_heap_x h p prog : CF.h_formula * CP.spec_var list               *)
(*      = match h with                                                             *)
(*  | Star {h_formula_star_h1 = h1;                                                *)
(*    h_formula_star_h2 = h2;                                                      *)
(*    h_formula_star_pos = pos} ->                                                 *)
(*    let h1,vars1 = simplify_heap h1 p prog in                                    *)
(*    let h2,vars2 = simplify_heap h2 p prog in                                    *)
(*    (mkStarH h1 h2 pos, vars1 @ vars2)                                           *)
(*  | Conj {h_formula_conj_h1 = h1;                                                *)
(*    h_formula_conj_h2 = h2;                                                      *)
(*    h_formula_conj_pos = pos} ->                                                 *)
(*    let h1,vars1 = simplify_heap h1 p prog in                                    *)
(*    let h2,vars2 = simplify_heap h2 p prog in                                    *)
(*    (mkConjH h1 h2 pos, vars1 @ vars2)                                           *)
(*  | Phase { h_formula_phase_rd = h1;                                             *)
(*    h_formula_phase_rw = h2;                                                     *)
(*    h_formula_phase_pos = pos} ->                                                *)
(*    let h1,vars1 = simplify_heap h1 p prog in                                    *)
(*    let h2,vars2 = simplify_heap h2 p prog in                                    *)
(*    (mkPhaseH h1 h2 pos, vars1 @ vars2)                                          *)
(*  | ViewNode v ->                                                                *)
(*    let mix_h,_,_,_ = xpure prog (formula_of_heap h no_pos) in                   *)
(*    let pure_h = MCP.pure_of_mix mix_h in                                        *)
(*    let disjs = CP.list_of_disjs pure_h in                                       *)
(*    let res = List.filter (fun d -> TP.is_sat_raw (CP.mkAnd d p no_pos)) disjs in*)
(*    begin                                                                        *)
(*      match res with                                                             *)
(*        | [] -> (HFalse,[])                                                      *)
(*        | hd::[] -> (HTrue,v.h_formula_view_node::v.h_formula_view_arguments)    *)
(*        | _ -> (h,[])                                                            *)
(*    end                                                                          *)
(*  | _ -> (h,[])                                                                  *)

(*and simplify_heap h p prog =                            *)
(*  let pr = Cprinter.string_of_h_formula in              *)
(*  let pr2 = Cprinter.string_of_pure_formula in          *)
(*  let pr3 = Cprinter.string_of_spec_var_list in         *)
(*  Debug.no_2 "simplify_heap" pr pr2 (pr_pair pr pr3)*)
(*      (fun _ _ -> simplify_heap_x h p prog) h p         *)

let rec simplify_heap_x h p prog : CF.h_formula = match h with
  | Star {h_formula_star_h1 = h1;
    h_formula_star_h2 = h2;
    h_formula_star_pos = pos} -> 
    let h1 = simplify_heap h1 p prog in
    let h2 = simplify_heap h2 p prog in
    mkStarH h1 h2 pos
  | Conj {h_formula_conj_h1 = h1;
    h_formula_conj_h2 = h2;
    h_formula_conj_pos = pos} -> 
    let h1 = simplify_heap h1 p prog in
    let h2 = simplify_heap h2 p prog in
    mkConjH h1 h2 pos
  | Phase { h_formula_phase_rd = h1;
    h_formula_phase_rw = h2;
    h_formula_phase_pos = pos} -> 
    let h1 = simplify_heap h1 p prog in
    let h2 = simplify_heap h2 p prog in
    mkPhaseH h1 h2 pos
  | ViewNode v ->
    let mix_h,_,_,_ = xpure prog (formula_of_heap h no_pos) in
    let pure_h = MCP.pure_of_mix mix_h in
    let disjs = CP.list_of_disjs pure_h in
    let res = List.filter (fun d -> TP.is_sat_raw (CP.mkAnd d p no_pos)) disjs in
    begin
      match res with
        | [] -> HFalse
        | hd::[] -> HTrue
        | _ -> h
    end 
  | _ -> h

and simplify_heap h p prog =
  let pr = Cprinter.string_of_h_formula in
  let pr2 = Cprinter.string_of_pure_formula in
  Debug.no_2 "simplify_heap" pr pr2 pr
      (fun _ _ -> simplify_heap_x h p prog) h p

(* TODO : simplification here relies too much on Omega.simplify *)
(* TODO : problematic with other kinds of constraints *)

let rec simplify_post_heap_only fml prog = match fml with
  | Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos} -> 
    Or {formula_or_f1 = simplify_post_heap_only f1 prog; 
        formula_or_f2 = simplify_post_heap_only f2 prog; 
        formula_or_pos = pos}
  | _ -> 
    let h, p, fl, b, t = split_components fml in
    let p = MCP.pure_of_mix p in
    let h = simplify_heap h p prog in
    mkBase h (MCP.mix_of_pure p) t fl b no_pos

let rec elim_heap h p pre_vars heap_vars = match h with
  | Star {h_formula_star_h1 = h1;
    h_formula_star_h2 = h2;
    h_formula_star_pos = pos} -> 
    let h1 = elim_heap h1 p pre_vars heap_vars in
    let h2 = elim_heap h2 p pre_vars heap_vars in
    mkStarH h1 h2 pos
  | Conj {h_formula_conj_h1 = h1;
    h_formula_conj_h2 = h2;
    h_formula_conj_pos = pos} -> 
    let h1 = elim_heap h1 p pre_vars heap_vars in
    let h2 = elim_heap h2 p pre_vars heap_vars in
    mkConjH h1 h2 pos
  | Phase { h_formula_phase_rd = h1;
    h_formula_phase_rw = h2;
    h_formula_phase_pos = pos} -> 
    let h1 = elim_heap h1 p pre_vars heap_vars in
    let h2 = elim_heap h2 p pre_vars heap_vars in
    mkPhaseH h1 h2 pos
  | ViewNode v ->
    let node_als = MCP.ptr_equations_without_null (MCP.mix_of_pure p) in
    let node_aset = CP.EMapSV.build_eset node_als in
    let alias = (CP.EMapSV.find_equiv_all v.h_formula_view_node node_aset) @ [v.h_formula_view_node] in
    let cond = (CP.intersect_x (CP.eq_spec_var_x) alias pre_vars = []) 
      && (List.length (CP.intersect_x (CP.eq_spec_var_x) alias heap_vars) <= (List.length alias)) 
      && not (CP.is_res_spec_var v.h_formula_view_node)
    in
    if cond then HTrue else h
  | DataNode d ->
    let node_als = MCP.ptr_equations_without_null (MCP.mix_of_pure p) in
    let node_aset = CP.EMapSV.build_eset node_als in
    let alias = (CP.EMapSV.find_equiv_all d.h_formula_data_node node_aset) @ [d.h_formula_data_node] in
    let cond = (CP.intersect_x (CP.eq_spec_var_x) alias pre_vars = []) 
      && (List.length (CP.intersect_x (CP.eq_spec_var_x) alias heap_vars) <= (List.length alias)) 
      && not (CP.is_res_spec_var d.h_formula_data_node)
    in
    if cond then HTrue else h
  | _ -> h

let eqFormula f1 f2 = match (f1,f2) with
  | (Base _, Base _) 
  | (Exists _, Exists _) -> 
    let h1,p1,fl1,b1,t1 = split_components f1 in
    let h2,p2,fl2,b2,t2 = split_components f2 in
    let p1 = MCP.pure_of_mix p1 in
    let p2 = MCP.pure_of_mix p2 in
    h1 = h2 && TP.imply_raw p1 p2 && TP.imply_raw p2 p1 && fl1=fl2 && b1=b2 && t1=t2
  | _ -> f1=f2

let rec simplify_post post_fml post_vars prog subst_fml pre_vars inf_post = match post_fml with
  | Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos} ->
    let (f1,pres1) = simplify_post f1 post_vars prog subst_fml pre_vars inf_post in
    let (f2,pres2) = simplify_post f2 post_vars prog subst_fml pre_vars inf_post in
    if eqFormula f1 f2 then (f1,pres1)
    else (Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos},pres1@pres2)
  | _ ->
    let h, p, fl, b, t = split_components post_fml in
    let p = MCP.pure_of_mix p in
    let h = if pre_vars = [] || not(inf_post) then h else elim_heap h p pre_vars (CF.h_fv h) in
    (*let post_vars = CP.diff_svl post_vars ((CF.h_fv h)@pre_vars) in*)
    let p,pre = begin
      match subst_fml with
      | None -> (TP.simplify_raw (CP.mkExists post_vars p None no_pos),[])
      | Some triples (*(rel, post, pre)*) ->
        if inf_post then
          let rels = CP.get_RelForm p in
          let p = CP.drop_rel_formula p in        
          let pres,posts = List.split (List.concat (List.map (fun (a1,a2,a3) -> if Gen.BList.mem_eq CP.equalFormula a1 rels
            then [(a3,a2)] else []) triples)) in
          let post = CP.conj_of_list posts no_pos in
          let pre = CP.conj_of_list pres no_pos in
          let p = CP.remove_dup_constraints (CP.mkAnd post (TP.simplify_raw (CP.mkExists post_vars p None no_pos)) no_pos) in
          (p,[pre])
        else
          let rels = CP.get_RelForm p in
          let pres,posts = List.split (List.concat (List.map (fun (a1,a2,a3) -> if Gen.BList.mem_eq CP.equalFormula a1 rels
            then [(a3,a2)] else []) triples)) in
          let pre = CP.conj_of_list pres no_pos in
          (*let pre = TP.simplify_raw (CP.mkExists (CP.diff_svl (CP.fv p)) pre None no_pos) in*)
          (*let pre = CP.wrap_exists_svl pre (CP.diff_svl (CP.fv p)) in
          let pre = Redlog.elim_exists_with_eq pre in
          let pre = CP.arith_simplify_new pre in*)
          (*print_endline ("PRE" ^ Cprinter.string_of_pure_formula pre);*)
          (p,[pre])
      end
    in
    (*print_endline ("VARS: " ^ Cprinter.string_of_spec_var_list pre_vars);*)
    (mkBase h (MCP.mix_of_pure p) t fl b no_pos,pre)

let simplify_post post_fml post_vars prog subst_fml pre_vars inf_post = 
  let pr = Cprinter.string_of_formula in
  let pr2 = Cprinter.string_of_spec_var_list in
  Debug.no_2 "simplify_post" pr pr2 (pr_pair pr (pr_list !CP.print_formula))
      (fun _ _ -> simplify_post post_fml post_vars prog subst_fml pre_vars inf_post) post_fml post_vars

let rec simplify_pre pre_fml = match pre_fml with
  | Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos} ->
    let f1 = simplify_pre f1 in
    let f2 = simplify_pre f2 in
    if f1 = f2 then f1
    else Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}
  | _ ->
    let h, p, fl, b, t = split_components pre_fml in
    let p1,p2 = List.partition CP.is_lexvar (CP.list_of_conjs (CP.remove_dup_constraints (MCP.pure_of_mix p))) in
    let p = CP.mkAnd (Inf.simplify_helper (CP.conj_of_list p2 no_pos)) (CP.conj_of_list p1 no_pos) no_pos in
    mkBase h (MCP.mix_of_pure p) t fl b no_pos
		
let simplify_pre pre_fml =
	let pr = !CF.print_formula in
	Debug.no_1 "simplify_pre" pr pr simplify_pre pre_fml
	
let rec simplify_relation (sp:struc_formula) subst_fml pre_vars post_vars prog inf_post: struc_formula * CP.formula list = 
  let res = List.map (fun s -> simplify_ext_relation s subst_fml pre_vars post_vars prog inf_post) sp in
  let new_sp, pres = List.split res in
  (new_sp, List.concat pres)

and simplify_ext_relation (sp:ext_formula) subst_fml pre_vars post_vars prog inf_post = 
  match sp with
    | ECase b ->
      let r = List.map (fun (p,s)->(p,
          let new_s,pres = simplify_relation s subst_fml pre_vars post_vars prog inf_post in
          if pres = [] then new_s
          else 
            try List.map2 CF.merge_ext_pre new_s (List.map (fun x -> CF.formula_of_pure_formula x no_pos) pres)
            with _ -> new_s
        )) b.formula_case_branches in
      (ECase {b with formula_case_branches = r},[])
    | EBase b ->
      let r,pres = simplify_relation b.formula_ext_continuation subst_fml pre_vars post_vars prog inf_post in      
      let base = if pres = [] then simplify_pre (b.formula_ext_base) else
          let pre = CP.conj_of_list pres no_pos in 
          let xpure_base,_,_,_ = xpure prog b.formula_ext_base in
          let check_fml = CP.mkAnd (MCP.pure_of_mix xpure_base) pre no_pos in
          if TP.is_sat_raw check_fml then
            simplify_pre (CF.normalize 1 b.formula_ext_base (CF.formula_of_pure_formula pre no_pos) no_pos)
          else b.formula_ext_base
      in
      (EBase {b with formula_ext_base = base; formula_ext_continuation = r}, [])
    | EAssume(svl,f,fl) ->
      let pvars = CF.fv f in
      let pvars = CP.diff_svl pvars post_vars in
      let pvars = CP.remove_dups_svl pvars in
      (*let vr = List.map CP.to_primed svl in
      let post_vars = CP.diff_svl post_vars vr in
      let post_vars = List.filter (fun v -> not(CP.is_res_spec_var v)) post_vars in
      let post_vars = CP.remove_dups_svl post_vars in*)
      let (new_f,pres) = simplify_post f pvars prog subst_fml pre_vars inf_post in
      (EAssume(svl,new_f,fl), pres)
    (*| EVariance b -> 
      (EVariance {b with formula_var_continuation = fst (simplify_ext_relation b.formula_var_continuation subst_fml prog)},[])*)
    | EInfer b -> report_error no_pos "Do not expect EInfer at this level"


