(*
created by L2
*)

open Globals
open Gen
open Exc.GTable
open Label_only

module C = Cast
module Err = Error
module I = Iast
module AS = Astsimp
module IF = Iformula
module IP = Ipure
module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module TI = Typeinfer

let sv_name = CP.name_of_spec_var

let transform_hp_rels_to_iviews iprog (hp_rels:( CF.hp_rel_def) list):(ident*I.view_decl) list =
(*CP.rel_cat * h_formula * formula*)
let norm_free_svl f0 args=
  let rec helper f=
    match f with
      | CF.Base fb -> let fr_svl = CP.diff_svl (List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CF.h_fv fb.CF.formula_base_heap)) args in
        if fr_svl = [] then (CF.Base fb)
        else CF.add_quantifiers fr_svl (CF.Base fb)
      | CF.Exists _ ->
            let qvars1, base1 = CF.split_quantifiers f in
            let base2 = helper base1 in
             CF.add_quantifiers qvars1 base2
      | CF.Or orf ->
           CF.Or {orf with CF.formula_or_f1 = helper orf.CF.formula_or_f1;
           CF.formula_or_f2 = helper orf.CF.formula_or_f2;
           }
  in
  helper f0
in
  List.fold_left (fun acc (rel_cat, hf,_,f_body)->
      match rel_cat with
	| CP.HPRelDefn (v,r,paras)->
              let _ = Debug.binfo_hprint (add_str "hp: " !CP.print_sv) v no_pos in
              let _ = Debug.binfo_hprint (add_str "r: " !CP.print_sv) r no_pos in
	      let vname = sv_name v in
	      let slf, vars, tvars = match hf with
		| CF.HRel (v1,el,_)->
		      if ((String.compare (sv_name v1) vname)!=0) then failwith "hrel name inconsistency\n"
		      else  (
                          let tvars = List.map (fun (CP.SpecVar (t, v, _))-> (t,v)) (r::paras) in
			  let vars  = List.map (fun (CP.SpecVar (_, v, p))-> (v^(match p with Primed -> "PRM"| _ -> ""))
                          ) (r::paras) in
			  match vars with
			    | h::t -> h,t, (List.tl tvars)
			    | []   -> failwith "unexpected number of arguments in inferred predicates\n"
                      )
	 	| _ -> failwith "unexpected heap formula instead of hrel node \n"
              in
              (*mkExist*)
              let f_body1 = norm_free_svl f_body (r::paras) in
	      let no_prm_body = CF.elim_prm f_body1 in
	      let new_body = CF.set_flow_in_formula_override {CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link =None} no_prm_body in
	      let i_body = AS.rev_trans_formula new_body in
	      let i_body = IF.subst [((slf,Unprimed),(self,Unprimed))] i_body in
	      let struc_body = IF.mkEBase [] [] [] i_body None (* false *) no_pos in
              let data_name = match CP.type_of_spec_var r with
                | Named id -> id
                | _ -> report_error no_pos "should be a data name"
              in
              let n_iview = {  I.view_name = vname;
              I.view_pos = no_pos;
	      I.view_data_name = data_name;
	      I.view_vars = vars;
	      I.view_labels = List.map (fun _ -> empty_spec_label) vars;
	      I.view_modes = List.map (fun _ -> ModeOut) vars ;
	      I.view_typed_vars =  tvars;
              I.view_kind = I.View_NORM;
              I.view_prop_extns = [];
	      I.view_pt_by_self  = [];
	      I.view_formula = struc_body;
	      I.view_inv_lock = None;
	      I.view_is_prim = false;
	      I.view_invariant = IP.mkTrue no_pos;
              I.view_mem = None;
	      I.view_materialized_vars = [];
	      I.try_case_inference = false; }
              in
	      (vname, n_iview)::acc
	| _ -> acc) [] hp_rels

let transform_hp_rels_to_iviews iprog hp_rels =
  let pr1 = pr_list (pr_pair pr_id Cprinter.string_of_hp_rel_def) in
  let pr2 = pr_list (pr_pair pr_id Iprinter.string_of_view_decl) in
  Debug.no_1 "transform_hp_rels_to_iviews" pr1 pr2 transform_hp_rels_to_iviews iprog hp_rels

let syn_hprel_x crem_hprels irem_hprels=
  let rec process_one chps res=
    match chps with
      | [] -> res
      | chp::rest ->
            try
              let _ = I.look_up_hp_def_raw (res@irem_hprels) chp.C.hp_name in
               process_one rest res
            with Not_found ->
                let n_ihp = {
                    I.hp_name = chp.C.hp_name;
                    I.hp_typed_inst_vars= List.map
                        (fun (CP.SpecVar (t,id,_), i) -> (t,id,i)) chp.C.hp_vars_inst;
                    I.hp_is_pre = chp.C.hp_is_pre;
                    I.hp_formula = IF.mkBase IF.HEmp (IP.mkTrue no_pos) top_flow [] no_pos;
                }
                in
                process_one rest (res@[n_ihp])
  in
  process_one crem_hprels []

let syn_hprel crem_hprels irem_hprels =
  let pr1 = pr_list_ln Iprinter.string_of_hp_decl in
  let pr2 = pr_list_ln Cprinter.string_of_hp_decl in
  Debug.no_2 "syn_hprel" pr2 pr1 pr1
      (fun _ _ -> syn_hprel_x crem_hprels irem_hprels)
      crem_hprels irem_hprels

let hn_trans vnames hn = match hn with
  | IF.HRel (id,args, pos)->
        if (List.exists (fun n-> (String.compare n id)==0) vnames) then
          let hvar,tl = match args with
            | (IP.Var (v,_))::tl-> v,tl
            | _ -> failwith "reverification failure due to too complex predicate arguments \n" in
          IF.HeapNode {
              IF.h_formula_heap_node = hvar;
              IF.h_formula_heap_name = id;
              IF.h_formula_heap_deref = 0;
              IF.h_formula_heap_derv = false;
              IF.h_formula_heap_imm = IF.ConstAnn(Mutable);
              IF.h_formula_heap_imm_param = [];
              IF.h_formula_heap_full = false;
              IF.h_formula_heap_with_inv = false;
              IF.h_formula_heap_perm = None;
              IF.h_formula_heap_arguments = tl;
              IF.h_formula_heap_pseudo_data = false;
              IF.h_formula_heap_label = None;
              IF.h_formula_heap_pos = pos}
        else hn
  | _ -> hn

let plugin_inferred_iviews views iprog =
  let vnames = List.map (fun (n,_)-> n) views in
  let vdecls = List.map (fun (_,prd)-> { prd with
      I.view_name = prd.I.view_name;
      I.view_formula = IF.struc_formula_trans_heap_node (hn_trans vnames) prd.I.view_formula}
  ) views
  in
  {iprog with
      I.prog_view_decls= iprog.I.prog_view_decls@vdecls;
  }

let plugin_inferred_iviews views iprog =
  let pr1 = pr_list (pr_pair pr_id pr_none) in
  Debug.no_1 "plugin_inferred_iviews" pr1 Iprinter.string_of_program
      (fun _ -> plugin_inferred_iviews views iprog) views

let trans_hprel_2_cview_x iprog cprog proc_name hpdefs:
      C.view_decl list * C.hp_decl list =
  (*TODO: topo sort hp_rels*)
  let hpdefs1 = hpdefs in
  let def_hps, hpdefs2 = List.fold_left (fun (ls1,ls2) ((hp_kind, _,_,_) as def) ->
        match hp_kind with
          |  CP.HPRelDefn (hp,_,_) -> (ls1@[hp], ls2@[def])
          | _ -> (ls1,ls2)
    ) ([],[]) (hpdefs1) in
  (*subst into views that transformed from unknown preds prev may still have
    unk preds in their defs.
  *)
  (*remove defined unknown*)
  let irem_hprels, idef_hprels = List.partition (fun hp1 ->
      not (List.exists (fun hp2 -> String.compare hp1.I.hp_name (CP.name_of_spec_var hp2) = 0) def_hps)
  ) iprog.I.prog_hp_decls in
  let crem_hprels, c_hprels_decl= List.partition (fun hp1 ->
      not (List.exists (fun hp2 -> String.compare hp1.C.hp_name (CP.name_of_spec_var hp2) = 0) def_hps)
  ) cprog.C.prog_hp_decls in
  (*
    unknown preds which generated by INFER exist in cprog but iprog.
    good time to push them in
  *)
  let irem_hprels1 = syn_hprel crem_hprels irem_hprels in
  let _ = iprog.I.prog_hp_decls <- iprog.I.prog_hp_decls@irem_hprels1 in
  (*convert to iview*)
  let pair_iviews = transform_hp_rels_to_iviews iprog hpdefs2 in
  (*subst hprel -> view in defs*)
  let n_iproc = plugin_inferred_iviews pair_iviews iprog in
  let _ = iprog.I.prog_view_decls <- n_iproc.I.prog_view_decls in
  let iviews, new_views = List.fold_left (fun (ls1,ls2) (id,iv) -> ((ls1@[iv]), (ls2@[id]))) ([],[]) pair_iviews in
  let _ = List.iter (AS.process_pred_def_4_iast iprog) iviews in
  (* let _ = iprog.Iast.prog_view_decls <- iprog.Iast.prog_view_decls@iviews in *)
  (*convert to cview*)
  let cviews = (AS.convert_pred_to_cast new_views iprog cprog) in
  let _ = cprog.C.prog_hp_decls <- crem_hprels in
  (*put back*)
  (* let _ = iprog.I.prog_hp_decls <- iprog.I.prog_hp_decls@idef_hprels in *)
  (* let _ = cprog.C.prog_hp_decls <- cprog.C.prog_hp_decls@cdef_hprels in *)
  (cviews,c_hprels_decl)

let trans_hprel_2_cview iprog cprog proc_name hp_rels :
      C.view_decl list * C.hp_decl list=
  let pr1 = pr_list_ln ( Cprinter.string_of_hp_rel_def) in
  let pr2 = pr_list_ln Cprinter.string_of_view_decl in
  let pr3 = pr_list_ln Cprinter.string_of_hp_decl in
  Debug.no_1 "trans_hprel_2_view" pr1 (pr_pair pr2 pr3)
      (fun _ -> trans_hprel_2_cview_x iprog cprog proc_name hp_rels)
      hp_rels


let trans_formula_hp_2_view_x iprog cprog proc_name in_hp_names chprels_decl f=
  let rec part_sv_from_pos ls n n_need rem=
    match ls with
      | [] -> report_error no_pos "sau.get_sv_from_pos"
      | sv1::rest -> if n = n_need then (sv1, rem@rest)
        else part_sv_from_pos rest (n+1) n_need (rem@[sv1])
  in
  let retrieve_root hp_name args=
    let rpos = C.get_proot_hp_def_raw chprels_decl
      hp_name in
    let r,paras = part_sv_from_pos args 0 rpos [] in
    (r,paras)
  in
  let hn_trans hn = match hn with
    | IF.HRel (id,args, pos)->
	  if (List.exists (fun n -> (String.compare n id)==0) in_hp_names) then
	    let hvar,tl = retrieve_root id args in
            let r = match hvar with
              | (IP.Var (v,_)) -> v
              | _ -> report_error no_pos "ASTSIMP.trans_formula_hp_2_view"
            in
            IF.HeapNode {
	        IF.h_formula_heap_node = r;
	        IF.h_formula_heap_name = id(* ^"_"^proc_name *);
                IF.h_formula_heap_deref = 0;
	        IF.h_formula_heap_derv = false;
	        IF.h_formula_heap_imm = IF.ConstAnn(Mutable);
                IF.h_formula_heap_imm_param = [];
	        IF.h_formula_heap_full = false;
	        IF.h_formula_heap_with_inv = false;
	        IF.h_formula_heap_perm = None;
	        IF.h_formula_heap_arguments = tl;
	        IF.h_formula_heap_pseudo_data = false;
	        IF.h_formula_heap_label = None;
	        IF.h_formula_heap_pos = pos}
	  else hn
    | _ -> hn
  in
  (*to improve*)
  (*revert to iformula*)
  let if1 = AS.rev_trans_formula f in
  (*trans hp -> view*)
  let if2 = IF.formula_trans_heap_node hn_trans if1 in
  (*trans iformula to cformula*)
  let if3 = AS.case_normalize_formula iprog [] if2 None in
  let n_tl = TI.gather_type_info_formula iprog if3 [] false in
  let _, f2 = AS.trans_formula iprog false [] false if3 n_tl false in
  f2

let trans_formula_hp_2_view iprog cprog proc_name in_hp_names chprels_decl f=
  let pr1= !CF.print_formula in
  let pr2 = pr_list pr_id in
  Debug.no_2 "trans_formula_hp_2_view" pr2 pr1 pr1
      (fun _ _ -> trans_formula_hp_2_view_x iprog cprog proc_name
          in_hp_names chprels_decl f)
      in_hp_names f
