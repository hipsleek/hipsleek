(* cview util
 this module contains procedures
  - transform between  cformula and cpure
  - relate to view
*)

open Globals
open Others
open Stat_global
open Exc.GTable
open Cast
open Prooftracer
open Gen.Basic

open Immutable
open Perm
open Cformula
open Mcpure_D
open Mcpure

(* let enable_distribution = ref true *)
let imp_no = ref 1


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
	    let simpl_f = Tpdispatcher.simplify_a 8 (CP.BForm(f,None)) in
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
	    let simpl_f = Tpdispatcher.simplify_a 7 (CP.BForm(f,None)) in
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
			let simpl_f = Tpdispatcher.simplify_a 6 (CP.BForm(f,None)) in
  		begin
  		match simpl_f with
  		| CP.BForm(simpl_f1,_) ->
  			(*let _ = print_string("\n[solver.ml]: Formula after simpl: " ^ Cprinter.string_of_b_formula simpl_f1 ^ "\n") in*)
  			simpl_f1
  		| _ -> f
  		end
  		else f
 	| _ -> f


let rec simpl_pure_formula (f : CP.formula) : CP.formula = match f with
  | CP.And (f1, f2, pos) -> CP.mkAnd (simpl_pure_formula f1) (simpl_pure_formula f2) pos
  | CP.AndList b -> CP.AndList (map_l_snd simpl_pure_formula b)
  | CP.Or (f1, f2, lbl, pos) -> CP.mkOr (simpl_pure_formula f1) (simpl_pure_formula f2) lbl pos
  | CP.Not (f1, lbl, pos) -> CP.mkNot (simpl_pure_formula f1) lbl pos
  | CP.Forall (sv, f1, lbl, pos) -> CP.mkForall [sv] (simpl_pure_formula f1) lbl pos
  | CP.Exists (sv, f1, lbl, pos) -> CP.mkExists [sv] (simpl_pure_formula f1) lbl pos
  | CP.BForm (f1,lbl) ->
        let simpl_f = CP.BForm(simpl_b_formula f1, lbl) in
	(*let _ = print_string("\n[solver.ml]: Formula before simpl: " ^ Cprinter.string_of_pure_formula f ^ "\n") in
	  let _ = print_string("\n[solver.ml]: Formula after simpl: " ^ Cprinter.string_of_pure_formula simpl_f ^ "\n") in*)
	simpl_f

(* find a subs that eliminates evars *)
(* remove identity subs *)
let build_subs_4_evars evars eset =
  let subs=CP.EMapSV.build_subs_4_evars evars eset in
  List.filter (fun (v1,v2) -> not(CP.eq_spec_var v1 v2)) subs

let build_subs_4_evars evars eset =
  let pr_sv = Cprinter.string_of_spec_var in
  let pr_svl = pr_list pr_sv in
  let pr_subs = pr_list (pr_pair pr_sv pr_sv) in
  let pr_eset = CP.EMapSV.string_of in
  Debug.no_2 "build_subs_4_evars" pr_svl pr_eset pr_subs build_subs_4_evars evars eset


let compute_subs_mem puref evars = 
  let (subs,_) = CP.get_all_vv_eqs puref in
  let eqset = CP.EMapSV.build_eset subs in
  let nsubs = build_subs_4_evars evars eqset in
  (* let subs1 = List.map (fun (v1,v2) -> *)
  (*     if Gen.BList.mem_eq CP.eq_spec_var v2 evars then (v2,v1) *)
  (*     else (v1,v2) *)
  (* ) subs in *)
  (* Debug.info_hprint (add_str "orig subs" pr_subs) subs no_pos; *)
  (* Debug.info_hprint (add_str "old_subs" pr_subs) subs1 no_pos; *)
  (* Debug.info_hprint (add_str "new_subs" pr_subs) nsubs no_pos; *)
  nsubs

let compute_subs_mem puref evars = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "compute_subs_mem" pr (add_str "evars" !CP.print_svl) (pr_list (pr_pair !CP.print_sv !CP.print_sv)) compute_subs_mem  puref evars  


(* andreeac: to add equality info *)
let compatible_ann (ann1: CP.ann list) (ann2: CP.ann list) : bool =
  if not(!Globals.allow_field_ann) then false else 
  let rec helper ann1 ann2 = 
  match ann1, ann2 with
    | [], [] -> true
    | (CP.ConstAnn(Accs))::t1, a::t2 
    | a::t1, (CP.ConstAnn(Accs))::t2 -> let compatible = helper t1 t2 in
				                        true && compatible
    | (CP.TempRes(a1,a2))::t1, a::t2 
    | a::t1, (CP.TempRes(a1,a2))::t2 -> let compatible = helper t1 t2 in
				                        (CP.eq_ann a a2) && compatible
    | _ -> false
  in helper ann1 ann2

(**************************************************************************)
(******************************* XPURE *****************************)
(**************************************************************************)
(* Transform dlist to pure formula *)
let dlist_2_pure diff = 
    let rec merge dlist =
      match dlist with
        | [] -> CP.mkTrue no_pos
        | x::xs -> List.fold_left (fun a y ->
              CP.mkAnd (CP.mkPure (CP.mkNeq x y no_pos)) a no_pos) (merge xs) xs
    in 
    let diff_l = List.map (fun dlist ->
        let dlist = List.map (fun x -> CP.mkVar x no_pos) dlist in
        merge dlist) diff.mem_formula_mset in
    let diff_l = CP.conj_of_list diff_l no_pos in
    let mf = MCP.mix_of_pure diff_l in
    mf

(* WN : this calculation on mem_formula need to be revamped *) 
let h_formula_2_mem_x (f : h_formula) (p0 : mix_formula) (evars : CP.spec_var list) prog : CF.mem_formula = 
  let  baga_helper imm sv = 
    if ((Immutable.isLend imm) && !Globals.baga_imm) then CP.DisjSetSV.mkEmpty
    else CP.DisjSetSV.singleton_dset sv in
  let rec helper f =
    (* for h_formula *)
    match f with
      | Star ({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos}) -> 
          Debug.tinfo_hprint (add_str "f" (fun f -> "#Star#" ^ Cprinter.string_of_h_formula f)) f pos;
          if (Perm.allow_perm ()) then
            (**** PERM >> **********)
            (* In the presence of permissions, compute in
               a more organized manner
            *)
	        let m1 = helper h1  in
	        let m2 = helper h2 in
	        let m = (CP.DisjSetSV.star_disj_set m1.mem_formula_mset m2.mem_formula_mset) in
	        let res = {mem_formula_mset = m;} in
	        res
          (*********<<PERM*************)
          else
            (* The below seems too ad-hoc. May need to be revised/generalized *)
            let res = 
              match h1 with
                | CF.DataNode { (* CF.h_formula_data_name = name1; *)
 		      CF.h_formula_data_node = v1;
                      CF.h_formula_data_imm  = imm1;
 		      CF.h_formula_data_param_imm = param_ann1;
 		  } -> 
                      Debug.tinfo_hprint (add_str "h1" (fun f -> "#DN#" ^ Cprinter.string_of_h_formula f)) h1 pos;
                      let res = 
                        match h2 with
                          | CF.DataNode { (* CF.h_formula_data_name = name2; *)
 		                CF.h_formula_data_node = v2;
                                CF.h_formula_data_imm  = imm2;
 		                CF.h_formula_data_param_imm = param_ann2; }  -> 
                                Debug.tinfo_hprint (add_str "h2" (fun f -> "#DN#" ^ Cprinter.string_of_h_formula f)) h2 pos;
                                let compatible = compatible_ann param_ann1 param_ann2 in
                                let sg1 = baga_helper imm1 v1 in
                                let sg2 = baga_helper imm2 v2 in
                                let mset = if compatible then CP.DisjSetSV.merge_disj_set sg1 sg2
                                else CP.DisjSetSV.star_disj_set sg1 sg2 in
	                        {mem_formula_mset = mset;}
                          | CF.Star {CF.h_formula_star_h1 = h3;
			    CF.h_formula_star_h2 = h4} ->  
                                Debug.tinfo_hprint (add_str "h2" (fun f -> "#Star#" ^ Cprinter.string_of_h_formula f)) h2 pos;
                                let mset_h1h3 = helper (CF.mkStarH h1 h3 no_pos) in
                                let mset_h1h4 = helper (CF.mkStarH h1 h4 no_pos) in
                                let mset_h2 = helper h2 in
                                let m = CP.DisjSetSV.merge_disj_set mset_h1h3.mem_formula_mset mset_h1h4.mem_formula_mset in
                                let mset2 = CP.DisjSetSV.merge_disj_set m mset_h2.mem_formula_mset in
                                {mem_formula_mset = mset2}
                                    (*| CF.StarMinus {CF.h_formula_starminus_h1 = h3;
			              CF.h_formula_starminus_h2 = h4} *)
                          | CF.Conj {CF.h_formula_conj_h1 = h3;
			    CF.h_formula_conj_h2 = h4} 			                 
                          | CF.ConjStar {CF.h_formula_conjstar_h1 = h3;
			    CF.h_formula_conjstar_h2 = h4}
                          | CF.ConjConj {CF.h_formula_conjconj_h1 = h3;
			    CF.h_formula_conjconj_h2 = h4}                   			                 
                          | CF.Phase {CF.h_formula_phase_rd = h3;
			    CF.h_formula_phase_rw = h4}->  
                                Debug.tinfo_hprint (add_str "h2" (fun f -> "#Conj/ConjStar/ConjConj/Phase#" ^ Cprinter.string_of_h_formula f)) h2 pos;
                                let mset_h1h3 = helper (CF.mkStarH h1 h3 no_pos) in
                                let mset_h1h4 = helper (CF.mkStarH h1 h4 no_pos) in
                                let mset_h2 = helper h2 in
                                let m = CP.DisjSetSV.conj_disj_set mset_h1h3.mem_formula_mset mset_h1h4.mem_formula_mset in
                                let mset2 = CP.DisjSetSV.merge_disj_set m mset_h2.mem_formula_mset in
                                {mem_formula_mset = mset2}
                          | _ -> 
                                Debug.tinfo_hprint (add_str "h2" (fun f -> "#_#" ^ Cprinter.string_of_h_formula f)) h2 pos;
                                let mset_h2 = helper h2 in
                                let sg = CP.DisjSetSV.singleton_dset v1 in
                                let m = CP.DisjSetSV.merge_disj_set mset_h2.mem_formula_mset sg in
                                {mem_formula_mset = m}
                      in
                      res
                | CF.Star {CF.h_formula_star_h1 = h11;
		  CF.h_formula_star_h2 = h12} ->
                      Debug.tinfo_hprint (add_str "h1" (fun f -> "#Star#" ^ Cprinter.string_of_h_formula f)) h1 pos;
                      let mset_h2 = helper h2 in
                      if CF.is_data h2 then 
                        let mset_h11 = helper (CF.mkStarH h11 h2 no_pos) in
                        let mset_h12 = helper  (CF.mkStarH h12 h2 no_pos) in
                        let m = CP.DisjSetSV.merge_disj_set mset_h11.mem_formula_mset mset_h12.mem_formula_mset in
                        let mset2 = CP.DisjSetSV.merge_disj_set m mset_h2.mem_formula_mset in
                        {mem_formula_mset = mset2}
                      else 
                        let mset_h1 = helper h1 in
                        let mset2 = CP.DisjSetSV.merge_disj_set mset_h1.mem_formula_mset mset_h2.mem_formula_mset in
                        {mem_formula_mset = mset2}
                            (*| CF.StarMinus {CF.h_formula_starminus_h1 = h11;
			      CF.h_formula_starminus_h2 = h12}*)                 
                | CF.Conj {CF.h_formula_conj_h1 = h11;
		  CF.h_formula_conj_h2 = h12} 
                | CF.ConjStar {CF.h_formula_conjstar_h1 = h11;
		  CF.h_formula_conjstar_h2 = h12}
                | CF.ConjConj {CF.h_formula_conjconj_h1 = h11;
		  CF.h_formula_conjconj_h2 = h12}			           			           
                | CF.Phase {CF.h_formula_phase_rd = h11;
		  CF.h_formula_phase_rw = h12}->  
                      Debug.tinfo_hprint (add_str "h1" (fun f -> "#Conj/ConjStar/ConjConj/Phase#" ^ Cprinter.string_of_h_formula f)) h1 pos;
                      let mset_h11h2 = helper (CF.mkStarH h11 h2 no_pos) in
                      let mset_h12h2 = helper (CF.mkStarH h12 h2 no_pos) in
                      let mset_h1 = helper h1 in
                      let m = CP.DisjSetSV.conj_disj_set mset_h11h2.mem_formula_mset mset_h12h2.mem_formula_mset in
                      let mset2 = CP.DisjSetSV.merge_disj_set m mset_h1.mem_formula_mset in
                      {mem_formula_mset = mset2}
                | _ ->  
                      Debug.tinfo_hprint (add_str "h1" (fun f -> "#_#" ^ Cprinter.string_of_h_formula f)) h1 pos;
                      let mset_h1 = helper h1 in
                      let mset_h2 = helper h2 in
                      let m = CP.DisjSetSV.star_disj_set mset_h1.mem_formula_mset mset_h2.mem_formula_mset in
                      {mem_formula_mset = m} in
	    (* let m1 = helper h1 in *)
	    (* let m2 = helper h2 in *)
	    (* let m = (CP.DisjSetSV.star_disj_set m1.mem_formula_mset m2.mem_formula_mset) in *)
	    (* let res = {mem_formula_mset = m;} in *)
	    res
      | Phase ({h_formula_phase_rd = h1;
	h_formula_phase_rw = h2;
	h_formula_phase_pos = pos})
              (* | StarMinus {h_formula_starminus_h1 = h1;
	         h_formula_starminus_h2 = h2;
	         h_formula_starminus_pos = pos}  *)
      | Conj ({h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;
	h_formula_conj_pos = pos})
      | ConjStar ({h_formula_conjstar_h1 = h1;
	h_formula_conjstar_h2 = h2;
	h_formula_conjstar_pos = pos})	    	     
      | ConjConj ({h_formula_conjconj_h1 = h1;
	h_formula_conjconj_h2 = h2;
	h_formula_conjconj_pos = pos}) ->
            Debug.tinfo_hprint (add_str "f" (fun f -> "#Conj/ConjStar/ConjConj/Phase#" ^ Cprinter.string_of_h_formula f)) f pos;
	    let m1 = helper h1  in
	    let m2 = helper h2 in
	    let m = (CP.DisjSetSV.merge_disj_set m1.mem_formula_mset m2.mem_formula_mset) in
	    {mem_formula_mset = m;}
      | ThreadNode _ ->
            (* cannot decide just based on the resource, hence empty *)
            {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
      | DataNode ({h_formula_data_node = p;
	h_formula_data_perm = perm;
	h_formula_data_imm = imm;
	h_formula_data_pos = pos}) ->
            Debug.tinfo_hprint (add_str "f" (fun f -> "#DN#" ^ Cprinter.string_of_h_formula f)) f pos;
          (*In the presence of fractional permission,
            p in memset only if frac=1.0 
            Therefore, we need pure information to prove*)
	        let new_mset = 
              match perm with
                | Some var ->
                    (match !Globals.perm with
                      | Bperm -> CP.DisjSetSV.mkEmpty (*TODO: ???*)
                      | _ ->
                        (*prove that p0 |- var=full_perm*)
                          let full_f = Perm.mkFullPerm_pure () (Cpure.get_var var) in
                          let f0 = MCP.pure_of_mix p0 in
                          Debug.devel_zprint (lazy ("h_formula_2_mem: [Begin] check fractional variable "^ (Cprinter.string_of_formula_exp var) ^ " is full_perm" ^"\n")) pos;
                          let res,_,_ = CP.imply_disj_orig [f0] full_f (TP.imply_one 24) imp_no in
                          Debug.devel_zprint (lazy ("h_formula_2_mem: [End] check fractional variable "^ (Cprinter.string_of_formula_exp var) ^ " is full_perm. ### res = " ^ (string_of_bool res) ^"\n")) pos;
                          if (res) then
                            CP.DisjSetSV.singleton_dset (p(*, CP.mkTrue pos*))
                          else [])
                | None ->
                        let cond_empty = ((Immutable.isLend imm) && !Globals.baga_imm) || List.mem p evars || perm<> None in
	                if cond_empty then CP.DisjSetSV.mkEmpty
	                else CP.DisjSetSV.singleton_dset (p(*, CP.mkTrue pos*)) 
            in
	        {mem_formula_mset = new_mset;}
      | ViewNode ({ h_formula_view_node = p;
        h_formula_view_name = c;
        h_formula_view_arguments = vs;
        h_formula_view_annot_arg = anns;
        h_formula_view_remaining_branches = lbl_lst;
	h_formula_view_perm = perm;
        h_formula_view_pos = pos}) ->
            Debug.tinfo_hprint (add_str "f" (fun f -> "#VN#" ^ Cprinter.string_of_h_formula f)) f pos;
            let ba = look_up_view_baga prog c p vs in
            let vdef = look_up_view_def pos prog.prog_view_decls c in
            let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
            let to_svs = p :: vs in
            (* let from_svs_ann = vdef.view_ann_params in *)
            (* let to_svs_ann = anns in *)
            (*TO DO: Temporarily ignore LOCK*)
	        let new_mset = 
              (match perm with
                | Some var ->
                    (*******************PERM>>*****************)
                    (*In the presence of fractional permission,
                      p in memset only if frac=1.0 
                      Therefore, we need pure information to prove*)
                    let full_f = Perm.mkFullPerm_pure () (Cpure.get_var var) in
                    (*prove that p0 |- var=full_perm*)
                    let f0 = MCP.pure_of_mix p0 in
                    Debug.devel_zprint (lazy ("h_formula_2_mem: [Begin] check fractional variable "^ (Cprinter.string_of_formula_exp var) ^ " is full_perm" ^"\n")) pos;
                    let res,_,_ = CP.imply_disj_orig [f0] full_f (TP.imply_one 25) imp_no in
                    Debug.devel_zprint (lazy ("h_formula_2_mem: [End] check fractional variable "^ (Cprinter.string_of_formula_exp var) ^ " is full_perm. ### res = " ^ (string_of_bool res) ^"\n")) pos;
                    if (res) then
                      (match lbl_lst with
                        |None ->
                            if List.mem p evars then CP.BagaSV.mkEmpty
	                        else ba 
                        | Some ls -> 
                            lookup_view_baga_with_subs ls vdef from_svs to_svs)
                    else []
                (*******************<<PERM*****************)
                | None ->
                    (* (match vdef.view_inv_lock with *)
                    (*   | Some f -> CP.BagaSV.mkEmpty *)
                    (*   | None -> *)
                          (match lbl_lst with
                            |None ->
                                if List.mem p evars then CP.BagaSV.mkEmpty
	                            else ba 
                            | Some ls -> 

                                lookup_view_baga_with_subs ls vdef from_svs to_svs))
            in
	        {mem_formula_mset = CP.DisjSetSV.one_list_dset new_mset;} 
      | StarMinus _
      | Hole _ -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
      | FrmHole _ -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
      | HRel _  ->{mem_formula_mset = CP.DisjSetSV.mkEmpty;}
      | HTrue  -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
      | HFalse -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
      | HEmp   -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}

    in
(* 	(\*a much simpler version of the above helper*\) *)
    let rec helper_simpl f =
      let node_lst = split_star_h f in
      let mapper f = match f with (*base cases, no * (StarH)  *)
	| StarMinus _ -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
	| Hole _ -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
        | FrmHole _ -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
	| HRel _  -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
	| HTrue  -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
	| HFalse -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
	| HEmp   -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
	| Phase {h_formula_phase_rd = h1;h_formula_phase_rw = h2;h_formula_phase_pos = pos}
	| Conj {h_formula_conj_h1 = h1;h_formula_conj_h2 = h2;h_formula_conj_pos = pos}
	| ConjStar {h_formula_conjstar_h1 = h1;h_formula_conjstar_h2 = h2;h_formula_conjstar_pos = pos}
	| ConjConj {h_formula_conjconj_h1 = h1;h_formula_conjconj_h2 = h2;h_formula_conjconj_pos = pos} ->
	      Debug.tinfo_hprint (add_str "f" (fun f -> "#Conj/ConjStar/ConjConj/Phase#" ^ Cprinter.string_of_h_formula f)) f pos;
	      let m1 = helper_simpl h1  in
	      let m2 = helper_simpl h2 in
	      {mem_formula_mset = CP.DisjSetSV.merge_disj_set m1.mem_formula_mset m2.mem_formula_mset;}
        | ThreadNode _ -> {mem_formula_mset = CP.DisjSetSV.mkEmpty;}
	| DataNode ({h_formula_data_node = p;h_formula_data_imm = imm;h_formula_data_perm = perm;h_formula_data_pos = pos}) ->
	      Debug.tinfo_hprint (add_str "f" (fun f -> "#DN#" ^ Cprinter.string_of_h_formula f)) f pos;
	      (* if List.mem p evars || perm<> None then *)
	      (*   {mem_formula_mset = CP.DisjSetSV.mkEmpty;} *)
	      (* else *)
	      (*   {mem_formula_mset = CP.DisjSetSV.singleton_dset p;} *)
              (*In the presence of fractional permission,
                p in memset only if frac=1.0 
                Therefore, we need pure information to prove*)
	      let new_mset = 
                match perm with
                  | Some var ->
                        (match !Globals.perm with
                          | Bperm -> CP.DisjSetSV.mkEmpty (*TODO: ???*)
                          | _ ->
                                (*prove that p0 |- var=full_perm*)
                                let full_f = Perm.mkFullPerm_pure () (Cpure.get_var var) in
                                let f0 = MCP.pure_of_mix p0 in
                                Debug.devel_zprint (lazy ("h_formula_2_mem: [Begin] check fractional variable "^ (Cprinter.string_of_formula_exp var) ^ " is full_perm" ^"\n")) pos;
                                let res,_,_ = CP.imply_disj_orig [f0] full_f (TP.imply_one 24) imp_no in
                                Debug.devel_zprint (lazy ("h_formula_2_mem: [End] check fractional variable "^ (Cprinter.string_of_formula_exp var) ^ " is full_perm. ### res = " ^ (string_of_bool res) ^"\n")) pos;
                                if (res) then
                                  CP.DisjSetSV.singleton_dset (p(*, CP.mkTrue pos*))
                                else [])
                  | None ->
                        let cond_empty = ((Immutable.isLend imm) && !Globals.baga_imm) || List.mem p evars || perm<> None in
	                if cond_empty then CP.DisjSetSV.mkEmpty
	                else CP.DisjSetSV.singleton_dset (p(*, CP.mkTrue pos*)) 
              in
	      {mem_formula_mset = new_mset;}
	| ViewNode ({ h_formula_view_node = p;h_formula_view_name = c;h_formula_view_arguments = vs; 
          h_formula_view_imm = imm;
	  h_formula_view_remaining_branches = lbl_lst;h_formula_view_perm = perm;	h_formula_view_pos = pos}) ->
	      Debug.tinfo_hprint (add_str "f" (fun f -> "#VN#" ^ Cprinter.string_of_h_formula f)) f pos;
	      (* let vdef = look_up_view_def pos prog.prog_view_decls c in *)
	      (* (\*TO DO: Temporarily ignore LOCK*\) *)
	      (* if  perm<> None then {mem_formula_mset =[]} *)
	      (* else *)
	      (*   (match vdef.view_inv_lock with *)
	      (*     | Some f -> *)
	      (*   	{mem_formula_mset =[]} *)
	      (*     | None -> *)
	      (*   	let new_mset = *)
	      (*   	  (match lbl_lst with *)
	      (*   	    |None -> *)
	      (*   		 if List.mem p evars then CP.BagaSV.mkEmpty *)
	      (*   		 else look_up_view_baga prog c p vs *)
	      (*   	    | Some ls -> *)
	      (*   		  let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in *)
	      (*   		  let to_svs = p :: vs in *)
	      (*   		  lookup_view_baga_with_subs ls vdef from_svs to_svs) in *)
	      (*   	{mem_formula_mset = CP.DisjSetSV.one_list_dset new_mset;} *)
	      (*   ) *)
              let ba = look_up_view_baga prog c p vs in
              let vdef = look_up_view_def pos prog.prog_view_decls c in
              let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
              let to_svs = p :: vs in
              (*TO DO: Temporarily ignore LOCK*)
	      let new_mset = 
                let cond_empty = ((Immutable.isLend imm) && !Globals.baga_imm) in
                if cond_empty then CP.BagaSV.mkEmpty (* this gives priority to imm over perm. *)
                else
                  (match perm with
                    | Some var ->
                          (*******************PERM>>*****************)
                          (*In the presence of fractional permission,
                            p in memset only if frac=1.0 
                            Therefore, we need pure information to prove*)
                          let full_f = Perm.mkFullPerm_pure () (Cpure.get_var var) in
                          (*prove that p0 |- var=full_perm*)
                          let f0 = MCP.pure_of_mix p0 in
                          Debug.devel_zprint (lazy ("h_formula_2_mem: [Begin] check fractional variable "^ (Cprinter.string_of_formula_exp var) ^ " is full_perm" ^"\n")) pos;
                          let res,_,_ = CP.imply_disj_orig [f0] full_f (TP.imply_one 25) imp_no in
                          Debug.devel_zprint (lazy ("h_formula_2_mem: [End] check fractional variable "^ (Cprinter.string_of_formula_exp var) ^ " is full_perm. ### res = " ^ (string_of_bool res) ^"\n")) pos;
                          if (res) then
                            (match lbl_lst with
                              |None ->
                                   if List.mem p evars then CP.BagaSV.mkEmpty
	                           else ba 
                              | Some ls -> 
                                    lookup_view_baga_with_subs ls vdef from_svs to_svs)
                          else []
                            (*******************<<PERM*****************)
                    | None ->
                          (* (match vdef.view_inv_lock with *)
                          (*   | Some f -> CP.BagaSV.mkEmpty *)
                          (*   | None -> *)
                          (match lbl_lst with
                            |None ->
                                 if List.mem p evars then CP.BagaSV.mkEmpty
	                         else ba 
                            | Some ls -> 
                                  lookup_view_baga_with_subs ls vdef from_svs to_svs))
              in
	      {mem_formula_mset = CP.DisjSetSV.one_list_dset new_mset;}  
	| Star _  -> report_error no_pos "solver: h_mem should not get star at this point" in
      let r = List.fold_left (fun a c-> CP.DisjSetSV.star_disj_set a (mapper c).mem_formula_mset) CP.DisjSetSV.mkEmpty node_lst in
      {mem_formula_mset = r} in
    (* let mf = (helper f) in *)
    let mf = if !simpl_memset then helper(*_simpl2*) f else helper_simpl f in
    {mem_formula_mset = (CP.DisjSetSV.remove_dups_disj_set mf.mem_formula_mset)}


let h_formula_2_mem (f : h_formula) (p : mix_formula) (evars : CP.spec_var list) prog : CF.mem_formula =
  (* let pr0 = Cprinter.string_of_spec_var in *)
  (* let pr_subs = pr_list (pr_pair pr0 pr0) in *)
  Debug.no_3 "h_formula_2_mem"  Cprinter.string_of_h_formula Cprinter.string_of_mix_formula Cprinter.string_of_spec_var_list Cprinter.string_of_mem_formula 
      (fun f p evars -> h_formula_2_mem_x f p evars prog) f p evars

let rec formula_2_mem_x (f : CF.formula) prog : CF.mem_formula = 
  (* for formula *)
  (* let _ = print_string("f = " ^ (Cprinter.string_of_formula f) ^ "\n") in *)
  let rec helper f =
    match f with
      | Base ({formula_base_heap = h;
	    formula_base_pure = p;
	    formula_base_pos = pos}) -> 
	        h_formula_2_mem h p [] prog
      | Exists ({formula_exists_qvars = qvars;
	    formula_exists_heap = qh;
	    formula_exists_pure = qp;
	    formula_exists_pos = pos}) ->
            let subs = compute_subs_mem (pure_of_mix qp) qvars in
            let mset = (h_formula_2_mem qh qp [] prog).mem_formula_mset in
            let mset = CP.DisjSetSV.mk_exist_dset qvars subs mset in
             { mem_formula_mset = mset }
      | Or ({formula_or_f1 = f1;
	    formula_or_f2 = f2;
	    formula_or_pos = pos}) ->
	    let m1 = helper f1  in
	    let m2 = helper f2  in 
	    {mem_formula_mset = (CP.DisjSetSV.or_disj_set m1.mem_formula_mset m2.mem_formula_mset)}
  in helper f

let formula_2_mem (f : formula) prog : CF.mem_formula = 
  Debug.no_1 "formula_2_mem" Cprinter.string_of_formula Cprinter.string_of_mem_formula
      (fun _ -> formula_2_mem_x f prog) f


let rec xpure_mem_enum (prog : prog_decl) (* is_conseq:bool *) (f0 : formula) : (mix_formula * CF.mem_formula) = 
  Debug.no_1 "xpure_mem_enum" Cprinter.string_of_formula (fun (a1,a2)->(Cprinter.string_of_mix_formula a1)^" # "^(Cprinter.string_of_mem_formula a2))
      (fun f0 -> xpure_mem_enum_x prog f0) f0

(* xpure approximation with memory enumeration *)
and xpure_mem_enum_x (prog : prog_decl) (f0 : formula) : (mix_formula * CF.mem_formula) = 
  (*use different xpure functions*)
  let rec xpure_helper  (prog : prog_decl) (f0 : formula) : mix_formula = 
    match f0 with
      | Or ({ formula_or_f1 = f1;
	formula_or_f2 = f2;
	formula_or_pos = pos}) ->
            let pf1 = xpure_helper prog f1 in
            let pf2 = xpure_helper prog f2 in
	    (mkOr_mems pf1 pf2 )

      | Base ({ formula_base_heap = h;
	formula_base_pure = p;
	formula_base_pos = pos}) ->
            let (ph,_) = xpure_heap_mem_enum prog h p 1 in
	    MCP.merge_mems p ph true
      | Exists ({ formula_exists_qvars = qvars;
	formula_exists_heap = qh;
	formula_exists_pure = qp;
	formula_exists_pos = pos}) ->
            let (pqh,_) = xpure_heap_mem_enum prog qh qp 1 in
            let tmp1 = MCP.merge_mems qp pqh true in
            MCP.memo_pure_push_exists qvars tmp1
  in
  (xpure_helper prog f0, formula_2_mem f0 prog)

  (* using baga_inv, e.g. bseg4.slk *)
and xpure_heap_enum_baga_a (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int) : CP.ef_pure_disj =
  (* let baga_map = CP.map_baga_invs in *)
  (* let arg_map = CP.view_args_map in *)
  let bp = (Mcpure.pure_of_mix p0) in
  let p_aset = CP.pure_ptr_equations bp in
  let p_aset = CP.EMapSV.build_eset p_aset in
  let efpd1 = Expure.build_ef_heap_formula h0 (* [([], p_aset, [])] *) (prog.Cast.prog_view_decls) in
  (* let efpd2 = Expure.build_ef_pure_formula bp in *)
  (* let efpd = Expure.EPureI.norm_disj (Expure.EPureI.mk_star_disj efpd1 efpd2) in *)
  Expure.EPureI.to_cpure_disj efpd1

and xpure_heap_enum_baga (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int) : CP.ef_pure_disj =
  Debug.no_2 "xpure_heap_enum_baga" Cprinter.string_of_h_formula Cprinter.string_of_mix_formula Cprinter.string_of_ef_pure_disj
      (fun _ _ -> xpure_heap_enum_baga_a (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int)) h0 p0

(*
conv_from_ef_disj@2
conv_from_ef_disj inp1 :[([self], u_14=y_15 & u_14=z & y_15=y & z_16=z),([self,u_14], z_16=y_15 & u_14=z & y_15=y & z_16=z)]
conv_from_ef_disj@2 EXIT: u_14=y_15 & u_14=z & y_15=y & z_16=z #  [[self]]

(([a,b],pure1) \/ [c],pure2) ==> (pure1 & a!=null & b!=null \/ pre2 & c!=null, [[a,b],[c]]) 
*)

(* TODO : we r converting epure --> formula here
   and therefore not using the syntactic imply!
*)

(* using the enum technique with epure *)
and conv_from_ef_disj_x (disj:CP.ef_pure_disj) : (MCP.mix_formula * CF.mem_formula)  =
  (* WN : this conversion is incomplete *)

  match disj with
    | [] -> (Mcpure.mkMFalse no_pos, CF.mk_mem_formula [])
    | _ -> let f = Expure.EPureI.ef_conv_enum_disj (Expure.EPureI.from_cpure_disj disj) in
    (* | _ -> let f = Expure.ef_conv_enum_disj disj in *)
      (MCP.mix_of_pure f,CF.mk_mem_formula [])

and conv_from_ef_disj disj =
  let pr =  (fun (a1,a2)-> (Cprinter.string_of_mix_formula a1)^" # "^(Cprinter.string_of_mem_formula a2)) in
  Debug.no_1 "conv_from_ef_disj" Cprinter.string_of_ef_pure_disj pr (fun _ -> conv_from_ef_disj_x disj) disj

and xpure_heap_mem_enum_new
      (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int) : (MCP.mix_formula * CF.mem_formula) 
      = 
  if !Globals.en_slc_ps || not(!Globals.gen_baga_inv) then
    (* using mcpure slicing - to fix *)
    xpure_heap_mem_enum_x (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int) 
  else
    (* to call xpure_heap_enum_baga *)
    if !Globals.baga_xpure then
      let disj = xpure_heap_enum_baga (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int) in
      let ans = conv_from_ef_disj disj in
      ans
    else
      xpure_heap_mem_enum_x (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int)

and xpure_heap_mem_enum(*_debug*) (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int) : (MCP.mix_formula * CF.mem_formula) =
  let pr =  (fun (a1,a2)-> (Cprinter.string_of_mix_formula a1)^" # "^(Cprinter.string_of_mem_formula a2)) in
  Debug.no_3 "xpure_heap_mem_enum" Cprinter.string_of_h_formula Cprinter.string_of_mix_formula string_of_int pr
      (fun _ _ _ -> xpure_heap_mem_enum_new prog h0 p0 which_xpure) h0 p0 which_xpure 

and xpure_heap_mem_enum_x (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int) : (MCP.mix_formula * CF.mem_formula) =
  let rec xpure_heap_helper (prog : prog_decl) (h0 : h_formula) (which_xpure :int) memset: MCP.mix_formula = 
    match h0 with
      | DataNode ({h_formula_data_node = p;
        h_formula_data_perm = perm;
	h_formula_data_pos = pos}) ->
            let i = fresh_int2 () in
            (* let non_null = CP.mkNeqNull p pos in *)
            (* let non_null = CP.mkEqVarInt p i pos in *)
            if not (Perm.allow_perm ()) then
              let non_null = CP.mkEqVarInt p i pos in
	      MCP.memoise_add_pure_N (MCP.mkMTrue pos) non_null
            else
              (*WITH PERMISSION*)
              let non_null = CP.mkNeqNull p pos in
              (* let eq_i = CP.mkEqVarInt p i pos in *)
              (*TO CHECK: temporarily change from eq_i to non_null *)
              let eq_i = non_null in
              (*LDK: add fractional invariant 0<f<=1, if applicable*)
              (match perm with
                | None -> MCP.memoise_add_pure_N (MCP.mkMTrue pos) eq_i (* full permission -> p=i*)
                | Some f ->
                      let inv = 
                        if CF.is_mem_mem_formula p memset then eq_i
                        else
                          non_null
                      in
                      MCP.memoise_add_pure_N (MCP.mkMTrue pos) (CP.mkAnd inv (mkPermInv () f) no_pos)
              )
      | ThreadNode {CF.h_formula_thread_resource = rsr}  ->
            (*Thread resource may be used for xpure*)
            let mf,_ =  xpure_mem_enum prog rsr in
            mf
      | ViewNode ({ h_formula_view_node = p;
	h_formula_view_name = c;
	h_formula_view_arguments = vs;
	h_formula_view_perm = perm;
	h_formula_view_remaining_branches = rm_br;
	h_formula_view_pos = pos}) ->
            let vdef = look_up_view_def pos prog.prog_view_decls c in
            (*add fractional invariant 0<f<=1, if applicable*)
            let frac_inv = match perm with
              | None -> CP.mkTrue pos
              | Some f -> mkPermInv () f in
            let inv_opt =  Cast.get_xpure_one vdef rm_br in
            (* let diff_flag = not(vdef.view_xpure_flag) in *)
            let _ = Debug.ninfo_hprint (add_str "diff_flag" string_of_bool) (!force_verbose_xpure) no_pos in
            let _ = Debug.ninfo_hprint (add_str "which_xpure" string_of_int) (which_xpure) no_pos in
             (*LDK: ??? be careful to handle frac var properly. 
               Currently, no fracvar in view definition*)
            let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
            let to_svs = p :: vs in
            let res =
              (match inv_opt with
                | None ->
                      let _ = Debug.ninfo_hprint (add_str "inv_opt" pr_id) "None" no_pos in
                      let inv = if !force_verbose_xpure && which_xpure =1 && not(vdef.view_xpure_flag) then vdef.view_x_formula else vdef.view_user_inv in
                      let subst_m_fun = MCP.subst_avoid_capture_memo(*_debug1*) from_svs to_svs in
                      subst_m_fun (MCP.memoise_add_pure_N inv frac_inv)
                      (* MCP.memoise_add_pure_N (MCP.mkMTrue pos) frac_inv *)
                | Some xp1 ->
                      let _ = Debug.ninfo_hprint (add_str "inv_opt" pr_id) "Some" no_pos in
                      let vinv = match which_xpure with
                        | -1 -> MCP.mkMTrue no_pos
                        | 0 -> vdef.view_user_inv
                        | _ ->  (* if !force_verbose_xpure &&  not(vdef.view_xpure_flag) then vdef.view_x_formula else *) xp1
                      in
                      (* let vinv = if ( which_xpure=1 && diff_flag) then vdef.view_x_formula else vdef.view_user_inv in *)
                       (*LDK: ??? be careful to handle frac var properly. 
                        Currently, no fracvar in view definition*)
                      (* let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in *)
                      (* let to_svs = p :: vs in *)
                      (*add fractional invariant*)
                      let frac_inv_mix = MCP.OnePF frac_inv in
                      let subst_m_fun = MCP.subst_avoid_capture_memo(*_debug1*) from_svs to_svs in
                      subst_m_fun (CF.add_mix_formula_to_mix_formula frac_inv_mix vinv))
            in
            (*res is the view invariant defined by users or
              inferred by the system*)
            (*if the ViewNode is a LOCK node, we add more information (p=i)
              because LOCK is similar to a datanode*)
            (*Handle LOCK ViewNode differently*)
            (match vdef.view_inv_lock with
              | Some f ->
                    if CF.is_mem_mem_formula p memset then 
                      (*full LOCK node*)
                      let non_null = CP.mkNeqNull p pos in
                      (* let i = fresh_int2 () in *)
                      (* let eq_i = CP.mkEqVarInt p i pos in *)
                      (* TO CHECK: temporarily use non-null*)
                      let eq_i = non_null in
                      MCP.memoise_add_pure_N (MCP.mkMTrue pos) eq_i (* full permission -> p=i*)
                    else
                      (*partial LOCK node*)
                      (*Because of fractional permissions, it is harder
                        to know whether two heap nodes are separated
                        A xpure_heap could try to identify separated
                        heap nodes (by using fractional permissions).
                        CURRENTLY, we take a simpler approach.
                        For any nodes x with frac<1, x is different from
                        any other nodes in memset. That is:
                        for all v in memset. v!=x

                        A better xpure could be:
                        forall x y. x_frac + y_frac>1 => x!=y
                      *)
                      let d = memset.mem_formula_mset in
                      let len = List.length d in
                      if (len=0) then res
                      else
                        let svars = List.hd d in
                        let ineqs = List.fold_left (fun mix_f sv ->
                            let neq_f = CP.mkNeqVar p sv no_pos in
                            MCP.memoise_add_pure_N mix_f neq_f) res svars
                        in
                        ineqs
              | None -> res)
      | Star ({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos})
              (*| StarMinus ({h_formula_starminus_h1 = h1;
	        h_formula_starminus_h2 = h2;
	        h_formula_starminus_pos = pos})*)
      | Phase ({h_formula_phase_rd = h1;
	h_formula_phase_rw = h2;
	h_formula_phase_pos = pos})
      | Conj ({h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;
	h_formula_conj_pos = pos})
      | ConjStar ({h_formula_conjstar_h1 = h1;
	h_formula_conjstar_h2 = h2;
	h_formula_conjstar_pos = pos})	    		
      | ConjConj ({h_formula_conjconj_h1 = h1;
	h_formula_conjconj_h2 = h2;
	h_formula_conjconj_pos = pos}) ->
            let ph1 = xpure_heap_helper prog h1 which_xpure memset in
            let ph2 = xpure_heap_helper prog h2 which_xpure memset in
            let _ = Debug.ninfo_hprint (add_str "ph1" !Cast.print_mix_formula) ph1 no_pos in
            let _ = Debug.ninfo_hprint (add_str "ph2" !Cast.print_mix_formula) ph2 no_pos in
            let _ = Debug.ninfo_hprint (add_str "memset" !CF.print_mem_formula) memset no_pos in
            MCP.merge_mems ph1 ph2 true
      | StarMinus _ 
      | HTrue  -> MCP.mkMTrue no_pos
      | HFalse -> MCP.mkMFalse no_pos
      | HEmp   -> MCP.mkMTrue no_pos
      | HRel _ -> MCP.mkMTrue no_pos (* report_error no_pos "[solver.ml]: xpure_heap_mem_enum_x" *)
      | Hole _ -> MCP.mkMTrue no_pos (*report_error no_pos "[solver.ml]: An immutability marker was encountered in the formula\n"*)
      | FrmHole _ -> MCP.mkMTrue no_pos
  in
  (* to build a subs here *)
  let memset = h_formula_2_mem h0 p0 [] prog in
  if (is_sat_mem_formula memset) then (xpure_heap_helper prog h0 which_xpure memset, memset)
  else
    (MCP.mkMFalse no_pos, memset)

and xpure_symbolic_slicing (prog : prog_decl) (f0 : formula) : (formula * CP.spec_var list * CF.mem_formula) =
  let pr1 = Cprinter.string_of_formula in
  let pr2 (a,b,c) = pr_pair pr1 Cprinter.string_of_mem_formula (a,c) in
  Debug.no_1 "xpure_symbolic_slicing" pr1 pr2 (xpure_symbolic_slicing_x prog) f0
      
(* Return a CF.formula instead of a flatten MCP formula, the heap parts is not complex *)	
(* this method is only called by compute_view *)
and xpure_symbolic_slicing_x (prog : prog_decl) (f0 : formula) : (formula * CP.spec_var list * CF.mem_formula) =
  let rec xpure_symbolic_helper (prog : prog_decl) (f0 : formula) : (formula * CP.spec_var list) =
    match f0 with
      | Or ({ formula_or_f1 = f1;
	formula_or_f2 = f2;
	formula_or_pos = pos }) ->
            let ipf1, avars1 = xpure_symbolic_helper prog f1 in
            let ipf2, avars2 = xpure_symbolic_helper prog f2 in
	    let res_form = mkOr ipf1 ipf2 pos in
            (res_form, (avars1 @ avars2))
      | Base b ->
	    let ({ formula_base_heap = h;
	    formula_base_pure = p;
	    formula_base_pos = pos }) = b in
            let ph, addrs, _ = xpure_heap_symbolic 2 prog h p 1 in
            let n_p = MCP.merge_mems p ph true in
	    (* Set a complex heap formula to a simpler one *)
	    let n_f0 = mkBase HEmp n_p TypeTrue (mkTrueFlow ()) [] pos in (* formula_of_mix_formula n_p *)
            (n_f0, addrs)
      | Exists e ->
	    let ({ formula_exists_qvars = qvars;
	    formula_exists_heap = qh;
	    formula_exists_pure = qp;
	    formula_exists_pos = pos}) = e in 
            let pqh, addrs', _ = xpure_heap_symbolic 3 prog qh qp 1 in
            let addrs = Gen.BList.difference_eq CP.eq_spec_var addrs' qvars in
            let n_qp = MCP.merge_mems qp pqh true in
            (* Set a complex heap formula to a simpler one *)
	    let n_f0 = mkExists qvars HEmp n_qp TypeTrue (mkTrueFlow ()) [] pos in
            (n_f0, addrs)
  in
  let pf, pa = xpure_symbolic_helper prog f0 in
  (pf, pa, formula_2_mem f0 prog)


and xpure_perm_x (prog : prog_decl) (h : h_formula) (p: mix_formula) : MCP.mix_formula =
  if (not (CF.is_complex_heap h)) then MCP.mkMTrue no_pos else
    let f = MCP.pure_of_mix p in
    let heaps = split_star_conjunctions h in
    (*remove HTrue nodes*)
    let heaps = List.filter (fun h ->
        match h with
          | HEmp
          | HTrue -> false
          | _ -> true) heaps
    in
    (*group nodes with equal names into a partition*)
    let rec fct heaps p =
      match heaps with
        | [] -> []
        | hx::hxs ->
              let res = fct hxs p in
              let hx_var = CF.get_node_var hx in
              (*partition res into those with equal names and others*)
              let res_eq,res_others = List.partition (fun part ->
                  if part=[] then false else
                    (* let anode = List.hd part in *)
                    let anode_vars = List.map (fun h ->  CF.get_node_var h) part in
                    let vars = List.map (fun v -> MCP.find_closure_mix_formula v p) anode_vars in
                    let vars = List.concat vars in
                    (* let _ = print_endline ("hx = " ^ (Cprinter.string_of_h_formula hx)) in *)
                    (* let _ = print_endline ("hx_var = " ^ (Cprinter.string_of_spec_var hx_var)) in *)
                    (* let _ = print_endline ("part = " ^ (pr_list Cprinter.string_of_h_formula part)) in *)

                    (* let _ = print_endline ("vars = " ^ (Cprinter.string_of_spec_var_list vars)) in *)
                    let b = List.exists (fun v -> CP.eq_spec_var v hx_var) vars in
                    if (b) then (*same group*) true else false
              ) res in
              let res_eq = List.concat res_eq in
              [(hx::res_eq)]@res_others
    in
    let partition heaps p =
      let pr_in = pr_list Cprinter.string_of_h_formula in
      let pr_out parts = (pr_list (fun part -> pr_list Cprinter.string_of_h_formula part) parts) in
      Debug.no_2 "partition" pr_in Cprinter.string_of_mix_formula pr_out 
          fct heaps p
    in
    (*[x1,x2],[x3,x4]*)
    let parts = partition heaps p in
    (*check if each partition are not equal*)
    (*e.g. f1+f2+f3+f4>1*)
    let rec check_x parts =
      match parts with
        | []
        | [_] -> MCP.mkMTrue no_pos
        | part1::part2::ps ->
              let res = check_x (part2::ps) in
              let p1_vars = List.map CF.get_node_var part1 in (*[x1,x2]*)
              let p1_perms = List.map CF.get_node_perm part1 in
              let is_p1_full =
                List.exists (fun v -> v=None) p1_perms
              in
              (* [f1,f2]*)
              let p1_perm_exps = List.concat (List.map Perm.get_cperm p1_perms) in

              let f1 = List.fold_left ( fun acc_f part ->
                  (*check a partition part1 agains another partition part*)
                  let p_vars = List.map CF.get_node_var part in (*[x3,x4]*)
                  let p_perms = List.map CF.get_node_perm part in
                  let is_p_full =
                    List.exists (fun v -> v=None) p_perms
                  in
                  if (is_p1_full || is_p_full) then
                    let np = CP.mkNeqVar (List.hd p_vars) (List.hd p1_vars) no_pos in
                    (mix_of_pure np)
                  else
                    (*TOCHECK: howabout None = full_perm*)
                    (*[f3,f4]*) 
                    let p_perm_exps = List.concat (List.map Perm.get_cperm p_perms) in
                    (* [f1,f2,f3,f4]*)
                    let vars = p_perm_exps@p1_perm_exps in
                    let res = 
                      if (vars=[] || not !Globals.precise_perm_xpure) then false
                      else
                        if (!Globals.perm = Bperm) then
                          (**********BPERM>>********************)
                          (*part1=x1::(c1,t1,a1),x2::(c2,t2,a2),x1=x2
                            part2=x3::(c3,t3,a3),x4::(c4,t4,a4),x3=x4
                            IMPLY:
                            t1=t2: otherwise fail
                            t3=t4: otherwise fail
                            t1!=t3 => x1!=x3
                            c1+c2+c3+c4>t1+a1+a2+t2+a3+a4
                          *)
                          let func e =
                            match e with
                              | Cpure.Bptriple ((c,t,a),_) -> (c,t,a)
                              | _ -> report_error no_pos ("xpure_perm: expecting Bptriple")
                          in
                          let p1_triples = List.map func p1_perm_exps in
                          let p_triples = List.map func p_perm_exps in
                          (*t1!t3*)
                          let _,t1,_ = List.hd p1_triples in
                          let _,t3,_ = List.hd p_triples in
                          (*t1!=t3*)
                          let neq_t1_t3 = CP.mkNeqVar t1 t3 no_pos in
                          (*c1+c2+...*)
                          let all_cs = List.map (fun (c,_,_) -> c) (p1_triples@p_triples) in
                          let all_sum_c = List.fold_left (fun pf v ->
                              let var = CP.Var (v,no_pos) in
                              CP.Add (pf,var,no_pos)
                          ) (CP.Var (List.hd all_cs,no_pos)) (List.tl all_cs)
                          in
                          (*a1+a2+...*)
                          let all_as = List.map (fun (_,_,a) -> a) (p1_triples@p_triples) in
                          let all_sum_a = List.fold_left (fun pf v ->
                              let var = CP.Var (v,no_pos) in
                              CP.Add (pf,var,no_pos)
                          ) (CP.Var (List.hd all_as,no_pos)) (List.tl all_as)
                          in
                          (*t1+a1+a2+t2+a3+a4*)
                          let t1_all_sum_a = CP.Add (CP.Var (t1,no_pos),all_sum_a,no_pos) in
                          let gt_bf = CP.Gt (all_sum_c,t1_all_sum_a,no_pos) in
                          let gt_f = CP.BForm ((gt_bf,None),None) in
                          let or_f = CP.mkOr neq_t1_t3 gt_f None no_pos in
		          Debug.devel_zprint (lazy ("xpure_perm: check: [Begin] check bounded permission constrainst: "^ (Cprinter.string_of_pure_formula or_f) ^ "\n")) no_pos;
		          let b,_,_ = CP.imply_disj_orig [f] or_f (TP.imply_one 100) imp_no in
		          Debug.devel_zprint (lazy ("xpure_perm: check: [End] check bounded permission constrainst "^(string_of_bool b)^" \n")) no_pos;
                          b
                              (**********<<BPERM********************)
                        else if (!Globals.perm = Dperm) then
                          (**********DPERM>>********************)
                          if (List.length vars)<2 then false
			  else 
			    let rec perm_f lv : CP.formula*CP.exp= match lv with 
			      | h::[] -> (f,h)
			      | h::l-> 
				    let conss, last = perm_f l in
				    let n_ex = CP.fresh_perm_var () in
				    let n_ex_var = (CP.mkVar n_ex no_pos) in
				    let v_exp = CP.mkAdd last h no_pos in
				    let new_eq = CP.mkEq v_exp n_ex_var no_pos in
				    CP.mkAnd (CP.mkPure new_eq) conss no_pos, n_ex_var
			      | [] -> failwith "this case has already been checked in the previous if"in
			    let nf, _ = perm_f vars in
			    Debug.devel_zprint (lazy ("xpure_perm: check: [Begin] check distinct fractional permission constrainst: "^ 
				(Cprinter.string_of_pure_formula nf) ^ "\n")) no_pos;
			    let b =  not (TP.is_sat_sub_no 8 nf (ref 0)) in
			    Debug.devel_zprint (lazy ("xpure_perm: check: [End] check distinct fractional permission constrainst "^(string_of_bool b)^" \n")) no_pos;
			    b
                                (**********<<DPERM********************)
                        else
                          (**********FPERM,CPERM,NONE>>********************)
			  (*construct and check the fractional sum, otherwise use a joins fact*)
			  let sum_exp = List.fold_left (fun e v ->
			      CP.mkAdd e v no_pos
			  ) (List.hd vars) (List.tl vars) in
			  let full_exp = CP.mkFConst 1.0 no_pos in
			  (*f1+f2+f2+f4>1.0*)
			  let gt_exp = CP.mkGtExp sum_exp full_exp no_pos in
			  Debug.devel_zprint (lazy ("xpure_perm: check: [Begin] check fractional permission constrainst: "^ (Cprinter.string_of_pure_formula gt_exp) ^ "\n")) no_pos;
			  let b,_,_ = CP.imply_disj_orig [f] gt_exp (TP.imply_one 101) imp_no in
			  Debug.devel_zprint (lazy ("xpure_perm: check: [End] check fractional permission constrainst \n")) no_pos;
			  b
                              (**********<<FPERM,CPERM,NONE********************)
                    in
                    if(res) then
                      (*x1=x2, x3=x4, x1!=x3*)
                      if (p_vars=[] || p1_vars=[]) then
                        let _ = print_endline ("xpure_perm: check: something wrong happened with heap nodes") in
                        MCP.mkMTrue no_pos
                      else
                        let np = CP.mkNeqVar (List.hd p_vars) (List.hd p1_vars) no_pos in
                        (mix_of_pure np)
                    else MCP.mkMTrue no_pos
              ) (MCP.mkMTrue no_pos) (part2::ps) in
              (* END List.fold_left ( fun acc_f part -> *)
              let nf = MCP.merge_mems res f1 true in
              nf
    in
    let rec check parts =
      let pr_in parts = (pr_list (fun part -> pr_list Cprinter.string_of_h_formula part) parts) in
      Debug.no_1 "check" pr_in (Cprinter.string_of_mix_formula)
          check_x parts
    in
    let frac_p = check parts in
    (*For bounded permission, for each partition,
      x::(c1,t1,a1) * x::(c2,t2,a2) --> t1=t2*)
    let check_consistency_x part =
      if (!Globals.perm = Bperm) then
        let perms = List.map CF.get_node_perm part in
        let perm_exps = List.concat (List.map Perm.get_cperm perms) in
        let func e =
          match e with
            | Cpure.Bptriple ((c,t,a),_) -> (c,t,a)
            | _ -> report_error no_pos ("xpure_perm: expecting Bptriple")
        in
        let triples = List.map func perm_exps in
        (match triples with
          | [] -> CP.mkTrue no_pos
          | (_,t,_)::xs ->
                (*for each permission total t1 in xs, t1=t *)
                List.fold_left (fun f (_,t1,_) ->
                    let f1 = CP.mkEqVar t t1 no_pos in
                    CP.mkAnd f f1 no_pos
                ) (CP.mkTrue no_pos) xs)
      else CP.mkTrue no_pos
    in
    let check_consistency part =
      Debug.no_1 "check_consistency"
          (pr_list Cprinter.string_of_h_formula) (Cprinter.string_of_pure_formula)
          check_consistency_x part
    in
    let c_fs = List.map check_consistency parts in
    let c_f = List.fold_left (fun res f -> CP.mkAnd res f no_pos) (CP.mkTrue no_pos) c_fs in
    let frac_p = MCP.memoise_add_pure_N frac_p c_f in
    frac_p

and xpure_perm (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) : MCP.mix_formula =
  Debug.no_2 "xpure_perm" Cprinter.string_of_h_formula Cprinter.string_of_mix_formula Cprinter.string_of_mix_formula
      (fun _ _ -> xpure_perm_x prog h0 p0) h0 p0


and xpure_symbolic i (prog : prog_decl) (h0 : formula) : (MCP.mix_formula  * CP.spec_var list * CF.mem_formula) = 
  Debug.no_1_num i "xpure_symbolic" Cprinter.string_of_formula 
      (fun (p1,vl,p4) -> (Cprinter.string_of_mix_formula p1)^"#"^(Cprinter.string_of_spec_var_list vl)^"#
"^(Cprinter.string_of_mem_formula p4)) 
      (fun h0 -> xpure_symbolic_orig prog h0) h0
      
(* xpure approximation without memory enumeration *)
and xpure_symbolic_orig (prog : prog_decl) (f0 : formula) : (MCP.mix_formula * CP.spec_var list * CF.mem_formula) =
  (*use different xpure functions*)
  let xpure_h = (* if (Perm.allow_perm ()) then xpure_heap_symbolic_perm else *) xpure_heap_symbolic 4 in (*TO CHECK: temporarily use xpure_heap_symbolic only*)
  let mset = formula_2_mem f0 prog in 
  let rec xpure_symbolic_helper (prog : prog_decl) (f0 : formula) : (MCP.mix_formula * CP.spec_var list) = match f0 with
    | Or ({ formula_or_f1 = f1;
      formula_or_f2 = f2;
      formula_or_pos = pos}) ->
          let ipf1, avars1 = xpure_symbolic_helper prog f1 in
          let ipf2, avars2 = xpure_symbolic_helper prog f2 in
          let res_form = MCP.mkOr_mems ipf1 ipf2  in
          (res_form, (avars1 @ avars2))
    | Base ({ formula_base_heap = h;
      formula_base_pure = p;
      formula_base_pos = pos}) ->
          let ph, addrs, _ = xpure_heap_symbolic 5 prog h p 1 in
          let n_p = MCP.merge_mems p ph true in
          (n_p, addrs)
    | Exists ({ formula_exists_qvars = qvars;
      formula_exists_heap = qh;
      formula_exists_pure = qp;
      formula_exists_pos = pos}) ->
          let pqh, addrs', _ = xpure_h prog qh qp 1 in
          let addrs = Gen.BList.difference_eq CP.eq_spec_var addrs' qvars in
          let tmp1 = MCP.merge_mems qp pqh true in
          let res_form = MCP.memo_pure_push_exists qvars tmp1 in
          (res_form, addrs) in
  let pf, pa = xpure_symbolic_helper prog f0 in
  (* let _ = Debug.info_hprint (add_str "pure pf" Cprinter.string_of_mix_formula) pf no_pos in *)
  (* let _ = Debug.info_hprint (add_str "pa" Cprinter.string_of_spec_var_list) pa no_pos in *)
  (* let _ = Debug.info_hprint (add_str "mset" Cprinter.string_of_mem_formula) mset no_pos in *)
  (pf, pa, mset)

and xpure_heap_symbolic i (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int) : (MCP.mix_formula * CP.spec_var list * CF.mem_formula) = 
  Debug.no_3_num i
      "xpure_heap_symbolic" 
      string_of_int
      Cprinter.string_of_h_formula
      Cprinter.string_of_mix_formula
      (fun (p1,p3,p4) -> (Cprinter.string_of_mix_formula p1)^"#"^(string_of_spec_var_list p3)^"#"^(Cprinter.string_of_mem_formula p4)
          ^string_of_bool(is_sat_mem_formula p4)) 
      (fun which_xpure h0 p0 -> xpure_heap_symbolic_x prog h0 p0 which_xpure) which_xpure h0 p0

and xpure_heap_symbolic_x (prog : prog_decl) (h0 : h_formula) (p0: mix_formula) (which_xpure :int) : (MCP.mix_formula * CP.spec_var list * CF.mem_formula) = 
  let memset = h_formula_2_mem h0 p0 [] prog in
  let ph, pa = xpure_heap_symbolic_i prog h0 which_xpure in
  if (is_sat_mem_formula memset) then (ph, pa, memset)
  else (MCP.mkMFalse no_pos, pa, memset)


and smart_same_flag = ref true 
  (* this flag is to indicate if xpure0 and xpure1 
     are semantically the same *)

and xpure_heap_symbolic_i (prog : prog_decl) (h0 : h_formula)  xp_no: (MCP.mix_formula * CP.spec_var list) = 
  (* let _ = smart_same_flag := true in *)
  let pr (a,b) = pr_triple Cprinter.string_of_mix_formula Cprinter.string_of_spec_var_list string_of_bool (a,b,!smart_same_flag) in
  Debug.no_2 "xpure_heap_symbolic_i" string_of_int 
      Cprinter.string_of_h_formula pr
      (fun xp_no h0 -> xpure_heap_symbolic_i_x prog h0 xp_no) xp_no h0

and xpure_heap_symbolic_i_x (prog : prog_decl) (h0 : h_formula) xp_no: (MCP.mix_formula *  CP.spec_var list) = 
  let rec helper h0 : (MCP.mix_formula *  CP.spec_var list) = match h0 with
    | ThreadNode {CF.h_formula_thread_resource = rsr}  ->
          (*Thread resource may be used for xpure*)
          let mf,svl,_ =  xpure_symbolic 5 prog rsr in
          (mf,svl)
    | DataNode ({ h_formula_data_node = p;
      h_formula_data_perm = perm;
      h_formula_data_label = lbl;
      h_formula_data_pos = pos}) ->
          let non_zero = CP.BForm ((CP.Neq (CP.Var (p, pos), CP.Null pos, pos), None), lbl) in
          (*LDK: add fractional invariant 0<f<=1, if applicable*)
          (match perm with
            | None -> (MCP.memoise_add_pure_N (MCP.mkMTrue pos) non_zero , [p])
            | Some f ->
                  let res = CP.mkAnd non_zero (mkPermInv () f) no_pos in
	          (MCP.memoise_add_pure_N (MCP.mkMTrue pos) res , [p]))

    | ViewNode ({ h_formula_view_node = p;
      h_formula_view_name = c;
      h_formula_view_perm = perm; (*Viewnode does not neccessary have invariant on fractional permission*)
      h_formula_view_arguments = vs;
      h_formula_view_remaining_branches = lbl_lst;
      h_formula_view_pos = pos}) ->
          let ba = look_up_view_baga prog c p vs in
          let vdef = look_up_view_def pos prog.prog_view_decls c in
          let diff_flag = not(vdef.view_xpure_flag) in
          let _ = if diff_flag then smart_same_flag := false in
          let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
          let to_svs = p :: vs in
		  let helper () = 
		    (*--imm only*)
                    (*LDK: add fractional invariant 0<f<=1, if applicable*)
		    let diff_flag = not(vdef.view_xpure_flag) in
                    let _ = if diff_flag then smart_same_flag := false in
                    let frac_inv = match perm with
                    | None -> CP.mkTrue pos
                    | Some f -> mkPermInv () f in
                    let _ = Debug.ninfo_hprint (add_str "diff_flag" string_of_bool) diff_flag no_pos in
                    let vinv = if (xp_no=1 && diff_flag) then vdef.view_x_formula else vdef.view_user_inv in
                    let _ = Debug.ninfo_hprint (add_str "vinv" !Cast.print_mix_formula) vinv no_pos in
                    (*add fractional invariant*)
                    let frac_inv_mix = MCP.OnePF frac_inv in
                    let vinv = CF.add_mix_formula_to_mix_formula frac_inv_mix vinv in
                    let subst_m_fun f = MCP.subst_avoid_capture_memo from_svs to_svs f in
                    let vinv1 = subst_m_fun vinv in
                    let _ = Debug.ninfo_hprint (add_str "vinv1" !Cast.print_mix_formula) vinv1 no_pos in
                    (vinv1, ba) in
                  (match lbl_lst with
                    | None -> helper ()
                    | Some ls -> if !force_verbose_xpure then helper ()
		      else
                        (*--imm and --eps *)
                        let ba = lookup_view_baga_with_subs ls vdef from_svs to_svs in
                        (MCP.mkMTrue no_pos, ba)
                  )
    | Star ({ h_formula_star_h1 = h1;
      h_formula_star_h2 = h2;
      h_formula_star_pos = pos}) ->
          let ph1, addrs1 = helper h1 in
          let ph2, addrs2 = helper h2 in
          let tmp1 = MCP.merge_mems ph1 ph2 true in
          let _ = Debug.ninfo_hprint (add_str "ph1" !Cast.print_mix_formula) ph1 no_pos in
          let _ = Debug.ninfo_hprint (add_str "ph2" !Cast.print_mix_formula) ph2 no_pos in
          let _ = Debug.ninfo_hprint (add_str "addrs1" !CP.print_svl) addrs1 no_pos in
          let _ = Debug.ninfo_hprint (add_str "addrs2" !CP.print_svl) addrs2 no_pos in
          (tmp1, addrs1 @ addrs2)
    | StarMinus ({ h_formula_starminus_h1 = h1;
      h_formula_starminus_h2 = h2;
      h_formula_starminus_pos = pos}) -> (mkMTrue no_pos, [])
          (*let ph1, addrs1 = helper h1 in
            let ph2, addrs2 = helper h2 in
            let tmp1 = MCP.merge_mems ph1 ph2 true in
            (tmp1, addrs1 @ addrs2)          *)
    | Phase ({ h_formula_phase_rd = h1;
      h_formula_phase_rw = h2;
      h_formula_phase_pos = pos}) 
    | Conj ({ h_formula_conj_h1 = h1;
      h_formula_conj_h2 = h2;
      h_formula_conj_pos = pos})
    | ConjStar ({ h_formula_conjstar_h1 = h1;
      h_formula_conjstar_h2 = h2;
      h_formula_conjstar_pos = pos})	  	  
    | ConjConj ({ h_formula_conjconj_h1 = h1;
      h_formula_conjconj_h2 = h2;
      h_formula_conjconj_pos = pos}) ->
          let ph1, addrs1 = helper h1 in
          let ph2, addrs2 = helper h2 in
          let tmp1 = merge_mems ph1 ph2 true in
          (tmp1, addrs1 @ addrs2)
    | HRel _ -> (mkMTrue no_pos, [])
    | HTrue  -> (mkMTrue no_pos, [])
    | Hole _ -> (mkMTrue no_pos, []) (* shouldn't get here *)
    | FrmHole _ -> (mkMTrue no_pos, [])
    | HFalse -> (mkMFalse no_pos, [])
    | HEmp   -> (mkMTrue no_pos, []) in
  helper h0

let xpure_heap_x (prog : prog_decl) (h0 : h_formula) (p0 : mix_formula) (which_xpure :int) : (mix_formula * CP.spec_var list * CF.mem_formula) =
  (* let h0 = merge_partial_h_formula h0 in *) (*this will not work with frac permissions*)
  if (!Globals.allow_imm) || (!Globals.allow_field_ann) then
    xpure_heap_symbolic 1 prog h0 p0 which_xpure
  else
    let a, c = xpure_heap_mem_enum prog h0 p0 which_xpure in
    (a, [], c)

let xpure_heap_new (prog : prog_decl) (h0 : h_formula) (p0 : mix_formula) (which_xpure :int) : (mix_formula * CP.spec_var list * CF.mem_formula) =
  let (mf,svl,diff) as x = xpure_heap_x prog h0 p0 which_xpure in
  if (!Globals.ineq_opt_flag) then x
  else
    let diff_m = dlist_2_pure diff in
    let mf = MCP.merge_mems mf diff_m true in
    (mf,svl,{mem_formula_mset = []})

(*For fractional permissons, the pure constraint of the LHS is required*)
let xpure_heap i (prog : prog_decl) (h0 : h_formula) (p0 : mix_formula) (which_xpure :int) : (mix_formula * CP.spec_var list * CF.mem_formula)=
  let _ = smart_same_flag := true in
  let pr (mf,svl,m) = (pr_triple Cprinter.string_of_mix_formula Cprinter.string_of_spec_var_list Cprinter.string_of_mem_formula (mf,svl,m))^"#"^(string_of_bool !smart_same_flag) in
  Debug.no_3_num i "xpure_heap"
      Cprinter.string_of_h_formula Cprinter.string_of_mix_formula string_of_int pr
      (fun _ _ _ -> xpure_heap_new prog h0 p0 which_xpure) h0 p0 which_xpure


(* TODO : if no complex & --eps then then return true else xpure1 generated;
   what if user invariant has a disjunct? *)
let xpure_x (prog : prog_decl) (f0 : formula) : (mix_formula * CP.spec_var list * CF.mem_formula) =
  (* print_string "calling xpure"; *)
  if (!Globals.allow_imm)||(!Globals.allow_field_ann) then
    xpure_symbolic 4 prog f0
  else
    let a, c = xpure_mem_enum prog f0 in
    (a, [], c)

let xpure (prog : prog_decl) (f0 : formula) : (mix_formula * CP.spec_var list * CF.mem_formula) =
  Debug.no_1 "xpure"
      Cprinter.string_of_formula
      (fun (r1, _, r4) -> (Cprinter.string_of_mix_formula r1) ^ "#" ^ (Cprinter.string_of_mem_formula r4))
      (fun f0 -> xpure_x prog f0) f0

(**************************************)
(****************END XPURE ***********)
(**************************************)

let rec xpure_consumed_pre_heap (prog : prog_decl) (h0 : h_formula) : CP.formula = match h0 with
  | ThreadNode t -> CP.mkTrue t.h_formula_thread_pos (*TOCHECK*)
  | DataNode b -> CP.mkTrue b.h_formula_data_pos
  | ViewNode ({ h_formula_view_node = p;
    h_formula_view_name = c;
    h_formula_view_arguments = vs;
    h_formula_view_pos = pos}) ->
        let vdef = look_up_view_def pos prog.prog_view_decls c in(* views have been ordered such that this dependency is respected *)
        let vinv = MCP.fold_mem_lst (CP.mkTrue no_pos) false true vdef.view_user_inv in
        let from_svs = CP.SpecVar (Named vdef.view_data_name, self, Unprimed) :: vdef.view_vars in
        let to_svs = p :: vs in
	CP.subst_avoid_capture from_svs to_svs vinv
  | Conj ({ h_formula_conj_h1 = h1;
    h_formula_conj_h2 = h2;
    h_formula_conj_pos = pos}) 
  | ConjStar ({ h_formula_conjstar_h1 = h1;
    h_formula_conjstar_h2 = h2;
    h_formula_conjstar_pos = pos})
  | ConjConj ({ h_formula_conjconj_h1 = h1;
    h_formula_conjconj_h2 = h2;
    h_formula_conjconj_pos = pos})	  	
  | Phase ({ h_formula_phase_rd = h1;
    h_formula_phase_rw = h2;
    h_formula_phase_pos = pos}) 
  | StarMinus ({ h_formula_starminus_h1 = h1;
    h_formula_starminus_h2 = h2;
    h_formula_starminus_pos = pos})	
  | Star ({ h_formula_star_h1 = h1;
    h_formula_star_h2 = h2;
    h_formula_star_pos = pos}) ->
        let ph1 = xpure_consumed_pre_heap prog h1 in
        let ph2 = xpure_consumed_pre_heap prog h2 in
        CP.mkAnd ph1 ph2 pos
  | HRel _ -> P.mkTrue no_pos
  | HTrue  -> P.mkTrue no_pos
  | HFalse -> P.mkFalse no_pos
  | HEmp   -> P.mkTrue no_pos
  | Hole _ -> P.mkTrue no_pos (* report_error no_pos ("[solver.ml]: Immutability annotation encountered\n") *)
  | FrmHole _ -> P.mkTrue no_pos

(* xpure of consumed precondition *)
let rec xpure_consumed_pre (prog : prog_decl) (f0 : formula) : CP.formula = match f0 with
  | Or ({ formula_or_f1 = f1;
    formula_or_f2 = f2;
    formula_or_pos = pos}) ->
        let ipf1 = xpure_consumed_pre prog f1 in
        let ipf2 = xpure_consumed_pre prog f2 in
        CP.mkOr ipf1 ipf2 None pos
  | Base ({formula_base_heap = h}) -> xpure_consumed_pre_heap prog h
  | Exists ({formula_exists_qvars = qvars;	formula_exists_heap = qh;}) ->
        CP.mkExists qvars (xpure_consumed_pre_heap prog qh) None no_pos


let heap_baga (prog : prog_decl) (h0 : h_formula): CP.spec_var list = 
  let rec helper h0 = match h0 with
    | ThreadNode ({ h_formula_thread_node = p;}) ->[p] (*TOCHECK*)
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
            (*| StarMinus ({ h_formula_starminus_h1 = h1;h_formula_starminus_h2 = h2})*)    
    | Phase ({ h_formula_phase_rd = h1;h_formula_phase_rw = h2;})
    | Conj ({ h_formula_conj_h1 = h1;h_formula_conj_h2 = h2;})     
    | ConjStar ({ h_formula_conjstar_h1 = h1;h_formula_conjstar_h2 = h2;})    
    | ConjConj ({ h_formula_conjconj_h1 = h1;h_formula_conjconj_h2 = h2;}) -> (helper h1) @ (helper h2)
    | Hole _ | FrmHole _ | HTrue | HFalse | HEmp | StarMinus _-> []
    | HRel _ -> [] (*Error.report_no_pattern ()*)	in
  helper h0

(********************************************************************)
(*******************************PRUNE-PRED **************************)
(********************************************************************)

(*******AUX PRED_PRUNE******)
let filter_prun_cond_x old_mem prun_cond rem_br = List.fold_left (fun (yes_prune, no_prune, new_mem) (p_cond, pr_branches)->        if (Gen.BList.subset_eq (=) rem_br pr_branches) then (yes_prune, no_prune,new_mem)
     else if ((List.length (Gen.BList.intersect_eq (=) pr_branches rem_br))=0) then (yes_prune, no_prune,new_mem)
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
	  | Some y_p ->(Gen.Profiling.inc_counter "syn_memo_hit";(y_p@yes_prune, no_prune,new_mem))
          | None -> (*decide if i ^ a = false*)
		let imp = 
		  let and_is = MCP.fold_mem_lst_cons (CP.BConst (true,no_pos), None) [corr] false true !Globals.enable_aggressive_prune in
                  let r = if (!Globals.enable_fast_imply) then false
                  else 
                    let r1,_,_ = TP.imply_msg_no_no and_is (CP.BForm (p_cond_n,None)) "prune_imply" "prune_imply" true None in
                    (if r1 then Gen.Profiling.inc_counter "imply_sem_prun_true"
                    else Gen.Profiling.inc_counter "imply_sem_prun_false";r1) in
                  r in
		if imp then (*there was a contradiction*)
		  let nyp = pr_branches@yes_prune in
                  let mem_w_fail = MCP.memoise_add_failed_memo new_mem p_cond_n in
                  (nyp,no_prune,mem_w_fail)
		else (yes_prune,(p_cond, pr_branches)::no_prune,new_mem)
    with | Not_found -> (yes_prune, (p_cond, pr_branches)::no_prune, new_mem)
) ([],[], old_mem) prun_cond


let filter_prun_cond old_mem prun_cond rem_br =
  let pr1 = Cprinter.string_of_memo_pure_formula in
  let pr2 = Cprinter.string_of_prune_conditions in
  let pr3 = pr_list string_of_formula_label in
  let pr_out = pr_triple pr3 pr2 pr1 in
  Debug.no_3 "filter_prun_cond" pr1 pr2 pr3 pr_out
      filter_prun_cond_x old_mem prun_cond rem_br

(*******AUX PRED_PRUNE******)
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
(*******AUX PRED_PRUNE******)

let prune_bar_node_simpl bd dn old_mem ba_crt = (*(DataNode dn, old_mem, false)*)
  let state_var,perm_var = List.hd dn.h_formula_data_arguments , dn.h_formula_data_perm in
  let rem_br = match dn.h_formula_data_remaining_branches with | Some l -> l | None -> bd.barrier_prune_branches in        
  if (List.length rem_br)<=1 then (DataNode{dn with h_formula_data_remaining_branches = Some rem_br;}, old_mem,false)
  else
    (*decide which prunes can be activated and drop the ones that are implied while keeping the old unknowns*)
    let state_prun_cond = List.map (fun (c,l)-> (CP.Eq(CP.Var (state_var,no_pos), CP.IConst (c,no_pos),no_pos),None),l) bd.barrier_prune_conditions_state in
    let l_prune1,_, new_mem2 = filter_prun_cond old_mem state_prun_cond rem_br in
    let l_prune2 = match perm_var with
      | None -> []
      | Some perm_v ->
	    let rel_slice = MCP.memo_find_relevant_slice [Cpure.get_var perm_v] new_mem2 in
	    let f = MCP.fold_mem_lst_cons (CP.BConst (true,no_pos), None) [rel_slice] false true false in
	    match CP.get_inst_tree (Cpure.get_var perm_v) f with
	      | None -> []
	      | Some ts -> 
		    let triggered = List.fold_left (fun a (c,l)-> if (Tree_shares.Ts.contains ts c) then a else l@a) [] bd.barrier_prune_conditions_perm in
		    List.filter (fun c-> List.mem c triggered) rem_br in
    let l_prune  = l_prune1 @ l_prune2 in
    (*l_prune : branches that will be dropped*)
    (*l_no_prune: constraints that overlap with the implied set or are part of the unknown, remaining prune conditions *)
    (*rem_br : formula_label list  -> remaining branches *)         
    if ((List.length l_prune)>0) then  
      let posib_dismised = Gen.BList.remove_dups_eq (=) l_prune in
      let rem_br_lst = List.filter (fun c -> not (List.mem c posib_dismised)) rem_br in
      if (rem_br_lst == []) then (DataNode {dn with h_formula_data_remaining_branches = Some rem_br;}, old_mem, true) (*(HFalse, MCP.mkMFalse_no_mix no_pos, true)*)
      else ( DataNode {dn with h_formula_data_remaining_branches = Some rem_br_lst;}, new_mem2, true)
    else match dn.h_formula_data_remaining_branches with
      | Some _ -> (DataNode dn,new_mem2, false)
      | None -> (DataNode {dn with  h_formula_data_remaining_branches = Some rem_br}, new_mem2, true)

let rec heap_prune_preds_x prog (hp:h_formula) (old_mem: memo_pure) ba_crt : (h_formula * memo_pure * bool)= 
  match hp with
    | Star s ->
          let ba1 =ba_crt@(heap_baga prog s.h_formula_star_h1) in
          let ba2 =ba_crt@(heap_baga prog s.h_formula_star_h2) in
          let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_star_h1 old_mem ba2 in
          let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_star_h2 mem1 ba1 in
          (mkStarH h1 h2 s.h_formula_star_pos, mem2 , (changed1 || changed2))
    | StarMinus s ->
          let ba1 =ba_crt@(heap_baga prog s.h_formula_starminus_h1) in
          let ba2 =ba_crt@(heap_baga prog s.h_formula_starminus_h2) in
          let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_starminus_h1 old_mem ba2 in
          let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_starminus_h2 mem1 ba1 in
          (mkStarMinusH h1 h2 s.h_formula_starminus_aliasing s.h_formula_starminus_pos 17, mem2 , (changed1 || changed2))          
    | Conj s ->
          let ba1 =ba_crt@(heap_baga prog s.h_formula_conj_h1) in
          let ba2 =ba_crt@(heap_baga prog s.h_formula_conj_h2) in
          let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_conj_h1 old_mem ba2 in
          let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_conj_h2 mem1 ba1 in
          (Conj {  
              h_formula_conj_h1 = h1;
              h_formula_conj_h2 = h2;
              h_formula_conj_pos = s.h_formula_conj_pos }, mem2, (changed1 or changed2) )
    | ConjStar s ->  
          let ba1 =ba_crt@(heap_baga prog s.h_formula_conjstar_h1) in
          let ba2 =ba_crt@(heap_baga prog s.h_formula_conjstar_h2) in
          let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_conjstar_h1 old_mem ba2 in
          let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_conjstar_h2 mem1 ba1 in
          (ConjStar {  
              h_formula_conjstar_h1 = h1;
              h_formula_conjstar_h2 = h2;
              h_formula_conjstar_pos = s.h_formula_conjstar_pos }, mem2, (changed1 || changed2) )
    | ConjConj s ->
          let ba1 =ba_crt@(heap_baga prog s.h_formula_conjconj_h1) in
          let ba2 =ba_crt@(heap_baga prog s.h_formula_conjconj_h2) in
          let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_conjconj_h1 old_mem ba2 in
          let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_conjconj_h2 mem1 ba1 in
          (ConjConj {  
              h_formula_conjconj_h1 = h1;
              h_formula_conjconj_h2 = h2;
              h_formula_conjconj_pos = s.h_formula_conjconj_pos }, mem2, (changed1 || changed2) )                 
    |Phase  s ->
         let ba1 =ba_crt@(heap_baga prog s.h_formula_phase_rd) in
         let ba2 =ba_crt@(heap_baga prog s.h_formula_phase_rw) in
         let h1, mem1, changed1  = heap_prune_preds_x prog s.h_formula_phase_rd old_mem ba2 in
         let h2, mem2, changed2  = heap_prune_preds_x prog s.h_formula_phase_rw mem1 ba1 in
         (Phase {  
             h_formula_phase_rd = h1;
             h_formula_phase_rw = h2;
             h_formula_phase_pos = s.h_formula_phase_pos }, mem2, (changed1 || changed2) )
    | Hole _ | FrmHole _
    | HRel _
    | HTrue
    | HFalse 
    | HEmp -> (hp, old_mem, false)
    | ThreadNode _ -> (hp, old_mem, false)  (*TOCHECK*)
    | DataNode d -> 
	  (try 
	    let bd = List.find (fun c-> (String.compare c.barrier_name d.h_formula_data_name) = 0) prog.prog_barrier_decls in
	    prune_bar_node_simpl bd d old_mem ba_crt
	  with 
	    | Not_found  -> match d.h_formula_data_remaining_branches with
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
            let l_prune,l_no_prune, new_mem2 = filter_prun_cond old_mem prun_cond rem_br in        
            let l_prune' = 
              let aliases = MCP.memo_get_asets ba_crt new_mem2 in
              let ba_crt = ba_crt@(List.concat(List.map (fun c->CP.EMapSV.find_equiv_all c aliases ) ba_crt)) in
              let n_l = List.filter (fun c-> 
		  try
		    let c_ba,_ = List.find (fun (_,d)-> c=d) v_def.view_prune_conditions_baga in
		    let c_ba = List.map (CP.subs_one zip) c_ba in
		    not (Gen.BList.disjoint_eq CP.eq_spec_var ba_crt c_ba)
		  with Not_found-> true) rem_br in
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


let heap_prune_preds prog (hp:h_formula) (old_mem: memo_pure) ba_crt : (h_formula * memo_pure * bool)= 
  let pr = Cprinter.string_of_h_formula in
  let pr1 = Cprinter.string_of_memo_pure_formula in
  let pr2 (h,o,r) = pr_triple Cprinter.string_of_h_formula pr1 string_of_bool (h,o,r) in
  Debug.no_2 "heap_prune_preds" pr pr1 pr2 (fun _ _ -> heap_prune_preds_x prog hp old_mem ba_crt) hp old_mem


let heap_prune_preds_mix prog (hp:h_formula) (old_mem:MCP.mix_formula): (h_formula*MCP.mix_formula*bool)= match old_mem with
  | MCP.MemoF f -> 
        let r1,r2,r3 = heap_prune_preds prog hp f [] in
        (r1, MCP.MemoF r2, r3)
  | MCP.OnePF _ -> (hp,old_mem,false)

let prune_preds_x prog (simp_b:bool) (f:formula):formula =
  let simp_b = simp_b && !Globals.enable_redundant_elim in 
  let imply_w f1 f2 = let r,_,_ = TP.imply_one 26 f1 f2 "elim_rc" false None in r in   
  let f_p_simp c = if simp_b then MCP.elim_redundant(*_debug*) (imply_w,TP.simplify_a 3) c else c in
  let rec fct i op oh = if (i== !Globals.prune_cnt_limit) then (op,oh)
  else
    let nh, mem, changed = heap_prune_preds_mix prog oh op in 
    if changed then fct (i+1) mem nh
    else ((match op with | MCP.MemoF f -> MCP.MemoF (MCP.reset_changed f)| _ -> op) ,oh) in
  (*prune concurrent threads*)
  let helper_one_formula one_f =
    let rp,rh = fct 0 one_f.formula_pure one_f.formula_heap in 
    let rp = f_p_simp rp in
    {one_f with formula_pure=rp;formula_heap=rh}
  in
  let rec helper_formulas f = match f with
    | Or o -> 
          let f1 = helper_formulas o.formula_or_f1 in
          let f2 = helper_formulas o.formula_or_f2 in
          mkOr f1 f2 o.formula_or_pos
              (*Or {o with formula_or_f1 = f1; formula_or_f2 = f2;}*)
    | Exists e ->    
          let rp,rh = fct 0 e.formula_exists_pure e.formula_exists_heap in 
          let rp = f_p_simp rp in
          let new_a = List.map helper_one_formula e.formula_exists_and in
          mkExists_w_lbl e.formula_exists_qvars rh rp 
              e.formula_exists_type e.formula_exists_flow new_a e.formula_exists_pos e.formula_exists_label
    | Base b ->
          let rp,rh = fct 0 b.formula_base_pure b.formula_base_heap in 
          (* let _ = print_endline ("\nprune_preds: before: rp = " ^ (Cprinter.string_of_mix_formula rp)) in *)
          let rp = f_p_simp rp in
          let new_a = List.map helper_one_formula b.formula_base_and in
          mkBase_w_lbl rh rp b.formula_base_type  b.formula_base_flow new_a b.formula_base_pos b.formula_base_label in
  (* if not !Globals.allow_pred_spec then f *)
  let helper_formulas f = 
    let p2 = Cprinter.string_of_formula in
    Debug.no_1 "helper_formulas" p2 p2 helper_formulas f in 
  if (isAnyConstFalse f) then f 
  else if !Globals.dis_ps then f
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

let prune_preds prog (simp_b:bool) (f:formula):formula =   
  let p1 = string_of_bool in
  let p2 = Cprinter.string_of_formula in
  Debug.no_2 "prune_preds" p1 p2 p2 (fun _ _ -> prune_preds_x prog simp_b f) simp_b f

let prune_pred_struc_x prog (simp_b:bool) f = 
  let rec helper f =
    if (is_no_heap_struc_formula f) then f
    else match f with
      | ECase c -> ECase {c with formula_case_branches = List.map (fun (c1,c2)-> (c1, helper c2)) c.formula_case_branches;}
      | EBase b -> EBase {b with formula_struc_base = prune_preds prog simp_b b.formula_struc_base;
            formula_struc_continuation = map_opt helper b.formula_struc_continuation}
      | EAssume b -> EAssume {b with
	    formula_assume_simpl = prune_preds prog simp_b b.formula_assume_simpl;
	    formula_assume_struc = helper b.formula_assume_struc;}
      | EInfer b -> EInfer {b with  formula_inf_continuation = helper b.formula_inf_continuation}
      | EList b -> EList (map_l_snd helper b)
  in
  helper f
      (*let _ = print_string ("prunning: "^(Cprinter.string_of_struc_formula f)^"\n") in*)


let prune_pred_struc prog (simp_b:bool) f = 
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_2 "prune_pred_struc" pr string_of_bool pr (fun _ _ -> prune_pred_struc_x prog simp_b f) f simp_b


(********************************************************************)
(*******************************END PRUNE-PRED **************************)
(********************************************************************)

  (************* REMOVE @L NODES FROM FORMULA ***************)
let remove_imm_from_heap_helper f h1 h2  =
  let h1, x1, m1 = f h1 in 
  let h2, x2, m2 = f h2 in
  let x = 
    match x1,x2 with
      | Some x, Some y -> Some (CF.add_mix_formula_to_mix_formula x y)
      | Some x, _ 
      | _, Some x      -> Some x
      | None, None     -> None
  in
  (* let m =  CP.DisjSetSV.merge_disj_set m1.mem_formula_mset m2.mem_formula_mset in *)
  (h1, h2, x, m1@m2)

let remove_imm_from_heap_formula prog p0 which_xpure imml fh = (* fh *)
  let rec remove_imm_from_heap_formula_helper prog p0 which_xpure imml fh =
    let fun_help =  (remove_imm_from_heap_formula_helper prog p0 which_xpure imml) in 
    match fh with
      | CF.Star h  -> 
            let h1, h2 = h.CF.h_formula_star_h1,  h.CF.h_formula_star_h2 in 
            let h1, h2, x, m = remove_imm_from_heap_helper fun_help h1 h2 in
            let fh = CF.Star {h with h_formula_star_h1 = h1; h_formula_star_h2 = h2;} in
            (fh, x,m)
      | CF.Conj h  -> 
            let h1, h2 =  h.CF.h_formula_conj_h1, h.CF.h_formula_conj_h2 in
            let h1, h2, x, m = remove_imm_from_heap_helper fun_help h1 h2 in
            let fh = CF.Conj {h with h_formula_conj_h1 = h1; h_formula_conj_h2 = h2;} in
            (fh, x,m)
      | CF.ConjStar h  -> 
            let h1, h2 = h.CF.h_formula_conjstar_h1, h.CF.h_formula_conjstar_h2 in
            let h1, h2, x, m = remove_imm_from_heap_helper fun_help h1 h2 in
            let fh = CF.ConjStar {h with h_formula_conjstar_h1 = h1; h_formula_conjstar_h2 = h2;} in
            (fh, x,m)
      | CF.ConjConj h  ->
            let h1, h2 = h.CF.h_formula_conjconj_h1, h.CF.h_formula_conjconj_h2 in
            let h1, h2, x, m = remove_imm_from_heap_helper fun_help h1 h2 in
            let fh = CF.ConjConj {h with h_formula_conjconj_h1 = h1; h_formula_conjconj_h2 = h2;} in
            (fh, x,m)
      | CF.Phase h -> 
            let h1, h2 = h.CF.h_formula_phase_rd, h.CF.h_formula_phase_rw in
            let h1, h2, x, m = remove_imm_from_heap_helper fun_help h1 h2 in
            let fh = CF.Phase {h with h_formula_phase_rd = h1; h_formula_phase_rw = h2;} in
            (fh, x,m)
      | CF.DataNode (h1) -> 
            (* if (Immutable.isLend h1.h_formula_data_imm) then *)
            if (CP.eq_ann imml h1.h_formula_data_imm) then
              (* let xpure, _  = xpure_heap_mem_enum prog fh p0 which_xpure in *)
              let xpure, _, _  = xpure_heap_symbolic 9 prog fh p0 which_xpure in
              (HEmp, Some xpure, [h1.h_formula_data_node])
            else (fh, None, [])
      | CF.ViewNode (h1) ->
            (* if (Immutable.isLend h1.h_formula_view_imm) then *)
            if (CP.eq_ann imml h1.h_formula_view_imm) then
              (* let xpure, _ = xpure_heap_mem_enum prog fh p0 which_xpure in *)
              let xpure, _, _  = xpure_heap_symbolic 10 prog fh p0 which_xpure in
              (HEmp, Some xpure, [h1.h_formula_view_node])
            else (fh, None, [])
      | _          -> (fh, None, [])
  in
  remove_imm_from_heap_formula_helper prog p0 which_xpure imml fh

let remove_imm_from_formula_x prog f imml = (* f *)
  let is_intersect_non_empty lst1 lst2 = 
    not(Gen.is_empty (Gen.BList.intersect_eq CP.eq_spec_var lst1 lst2)) in
  let fun_helper p h = 
    (* decide below the value for which_xpure (1 or 0) ? *)
    let disj = if not (CP.isAccs imml) then snd (xpure_heap_mem_enum prog h p 1) else {mem_formula_mset = []} in (* get the dijointness information *)
    let fh, x, removed_vars = remove_imm_from_heap_formula prog p 1 imml h in (* remove @L and retrieve xpure of removed nodes *)    
    let pure = match x with
      | Some pr -> MCP.merge_mems pr p true
      | None   -> p in
    (* filter disj so that it will contain only those sets related to the removed nodes *)
    let disj = List.filter (fun dl -> is_intersect_non_empty dl removed_vars ) disj.mem_formula_mset in
    let p_disj = dlist_2_pure {mem_formula_mset = disj} in
    let pure = MCP.merge_mems p_disj pure true in
    (fh, pure)
  in  
  let rec remove_imm_from_formula_helper prog f imml =
  match f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	  let rf1 = remove_imm_from_formula_helper prog f1 imml in
	  let rf2 = remove_imm_from_formula_helper prog f2 imml in
	  let resform = mkOr rf1 rf2 pos in
	  resform
    | Base fb ->
          let fh, pure = fun_helper fb.formula_base_pure fb.formula_base_heap in
          Base({fb with formula_base_heap = fh;  formula_base_pure = pure })
    | Exists fe ->
          let fh, pure = fun_helper fe.formula_exists_pure fe.formula_exists_heap in
          Exists({fe with formula_exists_heap = fh; formula_exists_pure = pure }) 
  in remove_imm_from_formula_helper prog f imml

let remove_imm_from_formula prog f imml =
  let pr = Cprinter.string_of_formula in 
  Debug.no_1 "remove_imm_from_formula" pr pr (fun _ -> remove_imm_from_formula_x prog f imml) f

let remove_imm_from_struc_formula prog f imml = (* f *)
  let rec helper sf  = 
    match sf with
      | EBase f   -> EBase {f with formula_struc_base = remove_imm_from_formula prog f.formula_struc_base imml }
      | EList l   -> EList (map_l_snd helper l)
      | ECase c   -> ECase {c with formula_case_branches = List.map (fun (c1,c2)-> (c1, helper c2)) c.formula_case_branches;}
      | EAssume b -> EAssume {b with
	    formula_assume_simpl = remove_imm_from_formula prog b.formula_assume_simpl imml;
	    formula_assume_struc = helper b.formula_assume_struc;}
      | EInfer b  -> EInfer {b with  formula_inf_continuation = helper b.formula_inf_continuation}
  in helper f

  (************* end REMOVE @L NODES FROM FORMULA  ***************)

(*
node_name is node_name of view_name,
assumption:
 - |view_seg_args| = 1
 - node_args = view_seg_args
*)
let get_oa_node_view_x prog seg_vnames=
  let get_oa res vname=
    let vdecl = Cast.look_up_view_def_raw 56 prog.Cast.prog_view_decls vname in
    let ddecl = Cast.look_up_data_def_raw prog.Cast.prog_data_decls vdecl.Cast.view_data_name in
    if List.length vdecl.Cast.view_cont_vars = 1 &&
      List.length vdecl.Cast.view_vars = List.length (List.filter (fun ((t,_),_) ->
          match t with
            | Named _ -> true
            | _ -> false
      ) ddecl.Cast.data_fields)
    then res@[(vname, vdecl.Cast.view_data_name)] else res
  in
  List.fold_left get_oa [] seg_vnames

let get_oa_node_view prog seg_vnames=
  let pr1 = pr_list pr_id in
  Debug.no_1 "get_oa_node_view" pr1 (pr_list (pr_pair pr_id pr_id))
      (fun _ -> get_oa_node_view_x prog seg_vnames) seg_vnames

(* =========== remove the node specified by sv and return the removed node, if found  ==========*)
let crop_h_formula_x (f: h_formula) (svl: CP.spec_var list): 
      (* removed node & new_h_formula *)
      ((h_formula list) * h_formula) = 

  let helper_remove h1 h2 f = 
    let rh1, nh1 = f h1 in
    let rh2, nh2 = f h2 in
    let rh = rh1@rh2 in
    let merge =
      match nh1, nh2 with
        | Some h0, None
        | None, Some h0      -> (true, (h0, HEmp))
        | Some nh1, Some nh2 -> (false, (nh1,nh2))
        | _                  -> (true, (HEmp, HEmp))
    in
    (rh, merge) in
  let rec helper f =
    match f with
      | CF.Star h      ->
            let rh, (merge,(nh1,nh2)) = helper_remove h.CF.h_formula_star_h1 h.CF.h_formula_star_h2 helper in
            let nh = if not(merge) then CF.Star{h with h_formula_star_h1 = nh1; h_formula_star_h2 = nh2;} else nh1 in
            (rh, Some nh)
      | CF.DataNode   ({h_formula_data_node = n})
      | CF.ViewNode   ({h_formula_view_node = n})
      | CF.ThreadNode ({h_formula_thread_node = n}) ->
            let rh, nh = if Gen.BList.mem_eq CP.eq_spec_var n svl then ([f], None) else ([], Some f) in
            (rh, nh)
      | _ ->  ([], Some f)
  in
  let res = helper f in
  let new_h = 
    match snd res with
      | Some h -> (fst res, h)
      | None   -> (fst res, HEmp)
  in new_h

let crop_h_formula (f: h_formula) (svl: CP.spec_var list): 
      (* removed node & new_h_formula *)
      ((h_formula list) * h_formula) = 
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = pr_list Cprinter.string_of_spec_var in
  let pr_out = pr_pair (add_str "removede nodes:" (pr_list pr1)) (add_str "remaining formula" pr1) in
  Debug.no_2 "crop_h_formula" pr1 pr2 pr_out  crop_h_formula_x f svl

(* =========== end- remove the node specified by sv and return the removed node  ==========*)
