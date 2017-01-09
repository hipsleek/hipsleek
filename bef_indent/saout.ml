#include "xdebug.cppo"
open VarGen
(*
created by L2
*)

open Globals
open Gen
open Exc.GTable
(* open Label_only *)

module C = Cast
module Err = Error
module I = Iast
(* module AS = Astsimp *)
module IF = Iformula
module IP = Ipure
module CF = Cformula
module CP = Cpure
module MCP = Mcpure
(* module TI = Typeinfer *)
module LO = Label_only.LOne

let sv_name = CP.name_of_spec_var

let transform_hp_rels_to_iviews iprog cprog (hp_rels:( CF.hp_rel_def) list):((ident *Typeinfer.spec_var_type_list )*I.view_decl) list =
(*CP.rel_cat * h_formula * formula*)
List.fold_left (fun acc (* (rel_cat, hf,_,f_body) *) def ->
    let f_body = CF.disj_of_list (List.map fst def.CF.def_rhs) no_pos in
    match def.CF.def_cat with
	| CP.HPRelDefn (v,r,paras)->
              (*pure preds, dont need to transform*)
              if List.for_all (fun sv -> not (CP.is_node_typ sv)) (r::paras) then acc else
              let () = Debug.ninfo_hprint (add_str "hp: " !CP.print_sv) v no_pos in
              let () = Debug.ninfo_hprint (add_str "r: " !CP.print_sv) r no_pos in
	      let vname = sv_name v in
	      let slf, vars, tvars = match def.CF.def_lhs with
		| CF.HRel (v1,el,_)->
		      if ((String.compare (sv_name v1) vname)!=0) then failwith "hrel name inconsistency\n"
		      else  (
                          let tvars = (List.map (fun (CP.SpecVar (t, v, _))-> (t,v)) (r::paras)) in
			  let vars  = List.map (fun (CP.SpecVar (_, v, p))-> (v^(match p with Primed -> "PRM"| _ -> ""))
                          ) (r::paras) in
			  match vars with
			    | h::t -> h,t, (List.tl tvars)
			    | []   -> failwith "unexpected number of arguments in inferred predicates\n"
                      )
	 	| _ -> failwith "unexpected heap formula instead of hrel node \n"
              in
              (*mkExist*)
              let data_name,r  = match CP.type_of_spec_var r with
                | Named id -> if String.compare id "" = 0  then
                    let n_id = C.get_root_typ_hprel cprog.C.prog_hp_decls (CP.name_of_spec_var v) in
                    let () = Debug.ninfo_hprint (add_str "n_id: " pr_id) n_id  no_pos in
                    let () = report_warning no_pos "sao: why is self's type null?" in
                    (n_id, (CP.SpecVar (Named n_id, CP.name_of_spec_var r, CP.primed_of_spec_var r)))
                  else
                    id,r
                | _ -> report_error no_pos "should be a data name"
              in
              let f_body1,tis = Cfutil.norm_free_vars f_body (r::paras) in
              let () = Debug.ninfo_hprint (add_str "f_body1: " Cprinter.prtt_string_of_formula) f_body1 no_pos in
              let no_prm_body = CF.elim_prm f_body1 in
	      let new_body = CF.set_flow_in_formula_override {CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link =None} no_prm_body in
              (* let new_body = CF.subst [] new_body0 in *)
	      let i_body = Rev_ast.rev_trans_formula new_body in
	      let i_body = IF.subst [((slf,Unprimed),(self,Unprimed))] i_body in
              let () = Debug.ninfo_hprint (add_str "i_body1: " Iprinter.string_of_formula) i_body no_pos in
	      let struc_body = IF.mkEBase [] [] [] i_body None (* false *) no_pos in
              let imm_map = Immutable.icollect_imm struc_body vars data_name iprog.I.prog_data_decls in
              let n_iview = {  I.view_name = vname;
              I.view_pos = no_pos;
	      I.view_data_name = data_name;
              I.view_type_of_self = None;
	      I.view_vars = vars;
	      I.view_ho_vars = []; (* TODO:HO *)
              (* I.view_imm_map = fst (List.fold_left (fun (r,n) _ -> (r@[(IP.ConstAnn Mutable, n)], n+1)) ([],0) vars); this serves as a bridge between the data field imm and the view param *)
              I.view_imm_map = imm_map;
	      I.view_labels = List.map (fun _ -> LO.unlabelled) vars, false;
	      I.view_modes = List.map (fun _ -> ModeOut) vars ;
	      I.view_typed_vars =  tvars;
              I.view_kind = I.View_NORM;
              I.view_derv = false;
              I.view_parent_name = None;
              I.view_prop_extns = [];
              I.view_derv_info = [];
	      I.view_pt_by_self  = [];
	      I.view_formula = struc_body;
	      I.view_inv_lock = None;
	      I.view_is_prim = false;
	      I.view_invariant = IP.mkTrue no_pos;
              I.view_baga_inv = None;
              I.view_baga_over_inv = None;
              I.view_baga_under_inv = None;
              I.view_mem = None;
	      I.view_materialized_vars = [];
	      I.try_case_inference = false; }
              in
	      ((vname,tis), n_iview)::acc
	| _ -> acc) [] hp_rels

let transform_hp_rels_to_iviews iprog cprog hp_rels =
  let pr1 = pr_list ( Cprinter.string_of_hp_rel_def) in
  let pr2 = pr_list (pr_pair (pr_pair pr_id Typeinfer.string_of_tlist) Iprinter.string_of_view_decl) in
  Debug.no_1 "transform_hp_rels_to_iviews" pr1 pr2
      (fun _ -> transform_hp_rels_to_iviews iprog cprog hp_rels) hp_rels

let syn_hprel_x crem_hprels irem_hprels=
  let rec process_one chps res=
    match chps with
      | [] -> res
      | chp::rest ->
            try
              let todo_unk = I.look_up_hp_def_raw (res@irem_hprels) chp.C.hp_name in
               process_one rest res
            with Not_found ->
                let n_ihp = {
                    I.hp_name = chp.C.hp_name;
                    I.hp_typed_inst_vars= List.map
                        (fun (CP.SpecVar (t,id,_), i) -> (t,id,i)) chp.C.hp_vars_inst;
                    I.hp_part_vars = chp.C.hp_part_vars;
                    I.hp_root_pos = chp.C.hp_root_pos;
                    I.hp_is_pre = chp.C.hp_is_pre;
                    I.hp_formula = IF.mkBase IF.HEmp (IP.mkTrue no_pos) IvpermUtils.empty_vperm_sets top_flow [] no_pos;
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

let hn_trans cprog vnames hn = match hn with
  | IF.HRel (id,eargs, pos)-> begin
        try
          if (List.exists (fun n-> (String.compare n id)==0) vnames) then
            let hvar,args =
              let er, args = C.get_root_args_hprel cprog.C.prog_hp_decls id eargs in
              let r = match er with
                | (IP.Var (sv,_))-> sv
                | IP.Ann_Exp (IP.Var (sv, _), _, _) -> sv (*annotated self*)
                | _ -> failwith "sao.hn_trans: reverification failure due to too complex predicate arguments \n"
              in
              (r, args)
            in
            IF.HeapNode {
                IF.h_formula_heap_node = hvar;
                IF.h_formula_heap_name = id;
                IF.h_formula_heap_deref = 0;
                IF.h_formula_heap_derv = false;
                IF.h_formula_heap_split = SPLIT0;
                IF.h_formula_heap_imm = IP.ConstAnn(Mutable);
                IF.h_formula_heap_imm_param = [];
                IF.h_formula_heap_full = false;
                IF.h_formula_heap_with_inv = false;
                IF.h_formula_heap_perm = None;
                IF.h_formula_heap_arguments = args;
                IF.h_formula_heap_ho_arguments = []; (* TODO:HO *)
                IF.h_formula_heap_pseudo_data = false;
                IF.h_formula_heap_label = None;
                IF.h_formula_heap_pos = pos}
          else hn
        with _ -> hn
    end
  | _ -> hn

let plugin_inferred_iviews views iprog cprog =
  let vnames = List.map (fun ((n,_),_)-> n) views in
  let () =  if !VarGen.sap then
    Debug.info_pprint (" views: " ^ ((pr_list pr_id) vnames)) no_pos
  else ()
  in
  let vdecls = List.map (fun (_,prd)-> { prd with
      I.view_name = prd.I.view_name;
      I.view_formula = IF.struc_formula_trans_heap_node (hn_trans cprog vnames) prd.I.view_formula}
  ) views
  in
  ({iprog with
      I.prog_view_decls= iprog.I.prog_view_decls(* @vdecls *);
  },vdecls)

let plugin_inferred_iviews views iprog cprog =
  let pr1 = pr_list (pr_pair (pr_pair pr_id pr_none) pr_none) in
  Debug.no_1 "plugin_inferred_iviews" pr1
      (pr_pair Iprinter.string_of_program pr_none)
      (fun _ -> plugin_inferred_iviews views iprog cprog) views

let trans_hprel_2_cview_x iprog cprog proc_name hpdefs:
      C.view_decl list * C.hp_decl list =
  (*TODO: topo sort hp_rels*)
  let hpdefs1 = hpdefs in
  let def_hps, hpdefs2, views = List.fold_left (fun (ls1,ls2, ls3) def ->
      match def.CF.def_cat with
        | CP.HPRelDefn (hp,_,_) -> begin
              let hp_name = CP.name_of_spec_var hp in
              try
                let () =  Debug.ninfo_pprint (" hp: " ^ (!CP.print_sv hp)) no_pos in
                let view = x_add C.look_up_view_def_raw 33 cprog.C.prog_view_decls hp_name in
                (ls1,ls2, ls3@[view])
              with _ -> (ls1@[hp], ls2@[def], ls3)
          end
         | _ -> (ls1,ls2, ls3)
  ) ([],[], []) (hpdefs1) in
  let () =  Debug.ninfo_pprint (" def_hps: " ^ (!CP.print_svl def_hps)) no_pos in
  if def_hps = [] then (views, [])
  else
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
  let irem_hprels1 = syn_hprel (crem_hprels@c_hprels_decl) irem_hprels in
  let () = iprog.I.prog_hp_decls <- iprog.I.prog_hp_decls@irem_hprels1 in
  (*convert to iview*)
  let pair_iviews = transform_hp_rels_to_iviews iprog cprog hpdefs2 in
  (*subst hprel -> view in defs*)
  let iviews0, new_views = List.fold_left (fun (ls1,ls2) (id,iv) -> ((ls1@[iv]), (ls2@[id]))) ([],[]) pair_iviews in
  let n_iproc,iviews = plugin_inferred_iviews pair_iviews iprog cprog in
  (* let () = iprog.I.prog_view_decls <- n_iproc.I.prog_view_decls in *)
  let () = List.iter (Astsimp.process_pred_def_4_iast iprog false) iviews in
  (* let () = iprog.Iast.prog_view_decls <- iprog.Iast.prog_view_decls@iviews in *)
  (*convert to cview. new_views: view with annotated types*)
  let cviews = (Astsimp.convert_pred_to_cast new_views false iprog cprog false) in
  let () = cprog.C.prog_hp_decls <- crem_hprels in
  (*put back*)
  (* let () = iprog.I.prog_hp_decls <- iprog.I.prog_hp_decls@idef_hprels in *)
  (* let () = cprog.C.prog_hp_decls <- cprog.C.prog_hp_decls@cdef_hprels in *)
  let () = if def_hps = [] then () else
     if !VarGen.sap then
       Debug.info_pprint (" transform: " ^ (!CP.print_svl def_hps) ^ "\n" )no_pos
     else ()
  in
  (cviews,c_hprels_decl)

let trans_hprel_2_cview iprog cprog proc_name hp_rels :
      C.view_decl list * C.hp_decl list=
  let pr1 = pr_list_ln ( Cprinter.string_of_hp_rel_def) in
  let pr2 = pr_list_ln Cprinter.string_of_view_decl in
  let pr3 = pr_list_ln Cprinter.string_of_hp_decl in
  Debug.no_1 "trans_hprel_2_cview" pr1 (pr_pair pr2 pr3)
      (fun _ -> trans_hprel_2_cview_x iprog cprog proc_name hp_rels)
      hp_rels


let trans_formula_hp_2_view_x iprog cprog proc_name chprels_decl hpdefs view_equivs f=
  (* let rec part_sv_from_pos ls n n_need rem= *)
  (*   match ls with *)
  (*     | [] -> report_error no_pos "sau.get_sv_from_pos" *)
  (*     | sv1::rest -> if n = n_need then (sv1, rem@rest) *)
  (*       else part_sv_from_pos rest (n+1) n_need (rem@[sv1]) *)
  (* in *)
  (* let retrieve_root hp_name args= *)
  (*   let rpos = C.get_proot_hp_def_raw chprels_decl *)
  (*     hp_name in *)
  (*   let r,paras = part_sv_from_pos args 0 rpos [] in *)
  (*   (r,paras) *)
  (* in *)
  let rec get_pos ls n sv=
    match ls with
      | [] -> report_error no_pos "sao.get_pos: impossible 1"
      | sv1::rest -> if CP.eq_spec_var sv sv1 then n
        else get_pos rest (n+1) sv
  in
  let rec get_pos_of_inter rest n inter_svl res=
    match rest with
      | [] -> res
      | sv1::rest -> if CP.mem_svl sv1  inter_svl then
          get_pos_of_inter rest (n+1) inter_svl (res@[n])
        else get_pos_of_inter rest (n+1) inter_svl res
  in
  let rec retreive_svl_of_inter_svl rest n inter_pos res=
    match rest with
      | [] -> res
      | sv1::rest ->let n_res=
          if Gen.BList.mem_eq (=) n  inter_pos then res@[sv1] else res
        in
        retreive_svl_of_inter_svl rest (n+1) inter_pos n_res
  in
  let rec partition_args_from_loc rem_args n r_pos non_root_args=
    match rem_args with
      | [] -> report_error no_pos "sa0:partition_args_from_loc"
      | sv::rest ->
            if n = r_pos then (sv, non_root_args@rest) else
              partition_args_from_loc rest (n+1) r_pos (non_root_args@[sv])
  in
  let rec look_up_root hpdefs hp act_args=
    match hpdefs with
      | [] -> None
      | def::rest -> begin
          match def.CF.def_cat with
            | CP.HPRelDefn (hp1, r, tl) ->
                  if CP.eq_spec_var hp hp1 then
                    let _,args = CF.extract_HRel def.CF.def_lhs in
                    let p = get_pos args 0 r in
                    Some (partition_args_from_loc act_args 0 p [])
                  else
                    look_up_root rest hp act_args
            | _ -> look_up_root rest hp act_args
          end
  in
  let get_args_w_useless hp args=
    try
      let def = CF.look_up_hp_def hpdefs hp in
      match def.CF.def_rhs with
        | [(f,_)] -> begin
            try
              let _,frm_args = CF.extract_HRel def.CF.def_lhs in
              let _,equiv_args = CF.extract_HRel_f f in
              if List.length frm_args = List.length equiv_args then args else
                let inter_pos = get_pos_of_inter frm_args 0 equiv_args [] in
                let inter_args = retreive_svl_of_inter_svl args 0 inter_pos [] in
                inter_args
            with _ -> args
          end
        | _ -> args
    with _ -> args
  in
  let hn_c_trans hn = match hn with
    | CF.HRel (hp,eargs, pos)-> begin
        let view_name0 = (CP.name_of_spec_var hp) in
        (*get equiv view name*)
        let view_name = try List.assoc view_name0 view_equivs
        with _ -> view_name0
        in
        let args0 = (List.fold_left List.append [] (List.map CP.afv eargs)) in
        let args =get_args_w_useless hp args0 in
        match look_up_root hpdefs hp args with
          | Some (r,tl) ->
	        (* let r,tl = C.get_root_args_hprel chprels_decl view_name args in *)
                CF.ViewNode {
	            CF.h_formula_view_node = r;
	            CF.h_formula_view_name = view_name;
                    CF.h_formula_view_derv = false;
                    CF.h_formula_view_split = SPLIT0;
	            CF.h_formula_view_imm = CP.ConstAnn(Mutable);
                    CF.h_formula_view_perm = None;
                    CF.h_formula_view_arguments = tl;
                    CF.h_formula_view_ho_arguments = []; (* TODO:HO *)
                    CF.h_formula_view_annot_arg = []; (* andreeac: this should not be [], but initialized based on view def. To check *)
                    CF.h_formula_view_args_orig = CP.initialize_positions_for_view_params (CP.sv_to_view_arg_list tl);
                    CF.h_formula_view_modes = [];
                    CF.h_formula_view_coercible = true;
                    CF.h_formula_view_origins = [];
                    CF.h_formula_view_original = true;
                    CF.h_formula_view_lhs_case = true;
                    CF.h_formula_view_unfold_num = 0;
                    CF.h_formula_view_label = None;
                    CF.h_formula_view_pruning_conditions = [];
                    CF.h_formula_view_remaining_branches = None;
	            CF.h_formula_view_pos = pos}
          | None -> hn
      end
    | _ -> hn
  in
  (*to improve*)
  (*revert to iformula*)
  (* let if1 = Astsimp.rev_trans_formula f in *)
  (* (\*trans hp -> view*\) *)
  (* let if2 = IF.formula_trans_heap_node hn_trans if1 in *)
  (* (\*trans iformula to cformula*\) *)
  (* let if3 = Astsimp.case_normalize_formula iprog [] if2 None in *)
  (* let n_tl = Typeinfer.gather_type_info_formula iprog if3 [] false in *)
  (* let _, f2 = Astsimp.trans_formula iprog false [] false if3 n_tl false in *)
  (* CF.elim_exists f2 *)
  CF.formula_trans_heap_node hn_c_trans f

let trans_formula_hp_2_view iprog cprog proc_name chprels_decl hpdefs view_equivs f=
  let pr1= !CF.print_formula in
  Debug.no_1 "trans_formula_hp_2_view" pr1 pr1
      (fun _ -> trans_formula_hp_2_view_x iprog cprog proc_name
          chprels_decl hpdefs view_equivs f)
       f

let trans_formula_view_2_hp_x iprog cprog proc_name view_names f=
  let rev_args r0 args0 hp_name=
    let rec do_put_root args n rp r res=
      match args with
        | [] -> res
        | a::rest ->
              if n==rp then (r::res)@args else
                do_put_root rest (n+1) rp r (res@[a])
    in
    try
      if args0 = [] then [r0] else
        let rp = C.get_proot_hp_def_raw cprog.C.prog_hp_decls hp_name in
        do_put_root args0 0 rp r0 []
    with _ -> r0::args0
  in
  let hn_rev_trans hn = match hn with
    | CF.ViewNode hv-> begin
        if Gen.BList.mem_eq (fun s1 s2 -> String.compare s1 s2 = 0) hv.CF.h_formula_view_name view_names then
          let r = hv.CF.h_formula_view_node in
          let all_args = rev_args r hv.CF.h_formula_view_arguments hv.CF.h_formula_view_name in
          CF.HRel (CP.SpecVar (HpT, hv.CF.h_formula_view_name, Unprimed),
          List.map (fun sv -> CP.mkVar sv hv.CF.h_formula_view_pos) all_args, hv.CF.h_formula_view_pos)
        else hn
      end
    | _ -> hn
  in
  CF.formula_trans_heap_node hn_rev_trans f

let trans_formula_view_2_hp iprog cprog proc_name view_names f=
  let pr1= !CF.print_formula in
  Debug.no_2 "trans_formula_view_2_hp" pr1 (pr_list pr_id) pr1
      (fun _ _ -> trans_formula_view_2_hp_x iprog cprog proc_name view_names f)
      f view_names

let trans_hp_def_view_2_hp_x iprog cprog proc_name in_hp_names hp_defs=
  let rev_formula_opt f_opt=
    match f_opt with
      | None -> None
      | Some f -> Some (trans_formula_view_2_hp iprog cprog proc_name in_hp_names f)
  in
  let rev_hp_def r hpdef=
    match hpdef.CF.def_cat with
      | CP.HPRelDefn (hp,_,_) ->
            let () = Debug.ninfo_hprint (add_str "hp" !CP.print_sv) hp no_pos in
            let ndef = if Gen.BList.mem_eq (fun s1 s2 -> String.compare s1 s2 = 0) (CP.name_of_spec_var hp) in_hp_names then
              hpdef
            else
              let nrhs = List.map (fun (f,og) -> (trans_formula_view_2_hp iprog cprog proc_name in_hp_names f,
              rev_formula_opt og) ) hpdef.CF.def_rhs in
              {hpdef with CF.def_rhs = nrhs}
            in
            r@[ndef]
      | _ -> r@[hpdef]
  in
  List.fold_left rev_hp_def [] hp_defs

let trans_hp_def_view_2_hp iprog cprog proc_name in_hp_names hp_defs=
  let pr1 =  pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list pr_id in
  Debug.no_2 "trans_hp_def_view_2_hp" pr2 pr1 pr1
      (fun _ _ -> trans_hp_def_view_2_hp_x iprog cprog proc_name in_hp_names hp_defs)
      in_hp_names hp_defs

(*******************************)
(***********REVERIFY************)
(*******************************)


let collect_hp_defs cprog= Hashtbl.fold (fun i p (acc1,acc2)->
    (p.C.proc_hpdefs@acc1, p.C.proc_sel_post_hps@acc2)) cprog.C.new_proc_decls ([],[])

let rec case_struc_formula_trans_x prog dang_hps to_unfold_hps pre_hps post_hps hpdefs struc_fnc formula_fct sf=
  (*********************************************************************************)
  let rec flow_partition hpdefs1 res=
    match hpdefs1 with
      | [] -> res
      | def::rest ->
            let part,rest1 =List.partition (fun def1 ->
                match def.CF.def_flow, def1.CF.def_flow with
                  | Some fl,Some fl1 ->
                        CF.equal_flow_interval fl fl1
                  | None, None -> true
                  | _ -> false
            ) rest in
            let nf = match def.CF.def_flow with
              | Some fl -> fl
              | None -> !norm_flow_int
            in
            flow_partition rest1 (res@[(nf,def::part)])
  in
  let rec partition_nf part_defs don=
    match part_defs with
      | [] -> raise Not_found
      | (fl,defs)::rest ->
            if CF.equal_flow_interval fl !norm_flow_int then
              ((fl,defs),don@rest)
            else partition_nf rest (don@[(fl,defs)])
  in
  let rec look_up_defs hp0 args basef1 parts (is_found,res)=
    let look_up (fl:Exc.GTable.nflow) def=
      match def.CF.def_cat with
        | CP.HPRelDefn (hp,_,_) -> if CP.eq_spec_var hp hp0 then
            let fs0 = (List.map fst def.CF.def_rhs) in
            let hps = List.fold_left (fun acc f -> acc@(CF.get_hp_rel_name_formula f)) [] fs0 in
            if CP.mem_svl hp hps then true,[] else
            let res1 = List.fold_left (fun r f ->
                let fs = CF.list_of_disjs f in
                let _,fm_args = CF.extract_HRel def.CF.def_lhs in
                let fs1= List.map (fun f1 ->
                    let ss = List.combine fm_args args in
                    let f2 =  (CF.subst ss f1) in
                    let basef2 = CF.subst ss basef1 in
                    let f4 = CF.mkStar f2 basef2 CF.Flow_combine (CF.pos_of_formula f2) in
                    let f5,ls_equans = CF.drop_hrel_f f4 dang_hps in
                    (fl, f5)
                ) fs
                in
                r@fs1
            ) [] fs0 in
            true,res1
          else false,[]
        | _ -> false,[]
    in
    match parts with
      | [] -> is_found,res
      | (ifl, defs)::rest -> begin
          let is_found1, acc = List.fold_left (fun (r1,r) def -> let is_found, defs = look_up ifl def in
          r1||is_found, r@defs
          ) (false,[]) defs in
          let acc1 = List.map (fun (fl,f) -> ([(ifl, defs)],fl, f)) acc in
          look_up_defs hp0 args basef1 rest ( is_found1||is_found,res@acc1)
        end
  in
  let case_detection_x iflow parts f0=
    let () =  Debug.ninfo_hprint (add_str "case_detection" (Cprinter.string_of_formula)) f0 no_pos in
    (* let hp_opt = CF.extract_hprel_pure f0 in *)
    let ls_hpargs = CF.get_HRels_f f0 in
    let f1,_ = CF.drop_hrel_f f0 (List.map fst ls_hpargs) in
    match ls_hpargs with
      | [] -> [(parts,iflow,f0)]
      |  [(hp,args)] -> begin
            let pos = (CF.pos_of_formula f0) in
            if CP.mem_svl hp dang_hps then
              (* let f1 = CF.formula_of_pure_N  p (\* CF.mkTrue_nf *\) pos in *)
              [(parts,iflow,f1)]
            else
              let is_found,pr_fs = look_up_defs hp args f1 parts (false,[]) in
              if not is_found && pr_fs =[] then
                begin
                  let f1,_ = CF.drop_hrel_f f0 [hp] in
                  let f2 = CF.substitute_flow_into_f iflow f1 in
                  [(parts, iflow, f2)]
                end
              else
                pr_fs 
              (* match pr_fs with *)
              (*   | [] -> begin *)
              (*       let f1,_ = CF.drop_hrel_f f0 [hp] in *)
              (*       let f2 = CF.substitute_flow_into_f iflow f1 in *)
              (*       [(parts, iflow, f2)] *)
              (*     end *)
              (*   | _ -> pr_fs *)
         end
      | _ -> let () = report_warning no_pos "saout:case_detection: multiple preds: not handle yet" in
        [(parts,iflow,f0)]
  in
  let case_detection iflow parts f0=
    let pr1 = Cprinter.string_of_formula in
    let pr2 = string_of_flow in
    let pr3 =  pr_list_ln Cprinter.string_of_hp_rel_def in
    let pr4 = (pr_list_ln (pr_pair pr2 pr3)) in
    Debug.no_3 "case_detection" pr2 pr4 pr1 (pr_list_ln (pr_triple pr4 pr2 pr1))
        (fun _ _ _ -> case_detection_x iflow parts f0)
        iflow parts f0
  in
  let formula_subst_dangling_pred_post dang_hps to_unfold_hps post_hps l_hpdefs iflow f0=
    let () =  Debug.ninfo_hprint (add_str "f0" (Cprinter.string_of_formula)) f0 no_pos in
    (* let () =  print_endline ("f0: " ^ (Cprinter.string_of_formula f0))  in *)
    let () =  Debug.ninfo_hprint (add_str "dang_hps" (!CP.print_svl)) dang_hps no_pos in
    let () =  Debug.ninfo_hprint (add_str "post_hps" (!CP.print_svl)) post_hps no_pos in
    let () =  Debug.ninfo_hprint (add_str " to_unfold_hps" (!CP.print_svl))  to_unfold_hps no_pos in
    (* let () =  print_endline (" to_unfold_hps : " ^ (!CP.print_svl  to_unfold_hps)) in *)
    (* let hp_opt = CF.extract_hrel_head_w_args f0 in *)
    try
      let hp_opt = CF. extract_hprel_pure f0 in
      match hp_opt with
        | None -> f0
        | Some (hp,args,p) -> let pos = (CF.pos_of_formula f0) in
          if CP.mem_svl hp dang_hps then CF.formula_of_pure_N  p (* CF.mkTrue_nf *) pos
          else
            try
                let hp_def = CF.look_up_hp_def l_hpdefs hp in
                if CP.mem_svl hp to_unfold_hps then
                  let f1 = CF.disj_of_list (List.map fst hp_def.CF.def_rhs) no_pos in
                  let _,fm_args = CF.extract_HRel hp_def.CF.def_lhs in
                  let ss = List.combine fm_args args in
                  let f2 =  (CF.subst ss f1) in
                  let f3= (* if CP.mem_svl hp post_hps then fresh_data_v f2 else *) f2 in
                  let p2 = CP.subst ss p in
                  let f4 = CF. mkAnd_pure f3 (MCP.mix_of_pure p2) pos in
                  let f5,ls_equans = CF.drop_hrel_f f4 dang_hps in
                  (* let quans = (List.fold_left List.append [] (List.map CP.afv (List.concat ls_equans))) in *)
                  (* let f6 = CF.add_quantifiers quans f5 in *)
                  let () =  Debug.ninfo_hprint (add_str "f5" (Cprinter.string_of_formula)) f5 no_pos in
                  (* let () =  print_endline ("f6: " ^ (Cprinter.string_of_formula f6))  in *)
                  f5
                else
                  CF.substitute_flow_into_f iflow f0
            with _ ->
                let f1,_ = CF.drop_hrel_f f0 [hp] in
                let f2 = CF.substitute_flow_into_f iflow f1 in
                f2
    with _ -> f0
  in
  let elim_dup_with_guard_x g sf=
    match sf with
      | CF.EBase b -> begin
          match b.CF.formula_struc_base with
            | CF.Base {formula_base_heap = h;
              formula_base_pure = mf;
              }
            | CF.Exists
                    {formula_exists_heap = h;
                    formula_exists_pure = mf;
                    } -> begin
                      let p = MCP.pure_of_mix mf in
                      if h = CF.HEmp && CP.equalFormula g p then
                        match b.CF.formula_struc_continuation with
                          | None -> sf
                          | Some sf1 -> sf1
                      else sf
                    end
            | _ -> sf
        end
      | _ -> sf
  in
  let elim_dup_with_guard g sf=
    let pr1 = Cprinter.string_of_struc_formula in
    let pr2 = Cprinter.string_of_pure_formula in
    Debug.no_2 "elim_dup_with_guard" pr2 pr1 pr1
        (fun _ _ ->  elim_dup_with_guard_x g sf) g sf
  in
  (*if can not find a post def in iflow, return true & __flow iflow*)
  let rec gen_case_spec parts ifl sf=
    let recf = gen_case_spec in
    let rec_pre parts1 fl b f1 = CF.EBase {b with
	CF.formula_struc_continuation = Gen.map_opt (recf parts1 fl) b.CF.formula_struc_continuation;
        CF.formula_struc_implicit_inst =  CP.remove_dups_svl (b.CF.formula_struc_implicit_inst@(CF.fresh_data_v_no_change  b.CF.formula_struc_base));
	CF.formula_struc_base = f1;
    }
    in
    match sf with
    | CF.ECase b-> CF.ECase {b with CF.formula_case_branches= Gen.map_l_snd (recf parts ifl) b.CF.formula_case_branches}
    | CF.EBase b -> begin
        let ls_hpargs = CF.get_HRels_f b.formula_struc_base in
        let pos = CF.pos_of_formula b.formula_struc_base in
        match ls_hpargs with
          |  [(hp,args)] -> begin
               let f1,_ = CF.drop_hrel_f b.formula_struc_base [hp] in
               let hfbase = CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, pos) in
               let f1base = CF.formula_of_heap hfbase pos in
               let pr_fl_fs= case_detection ifl parts f1base in
               match pr_fl_fs with
                 | [] ->  rec_pre parts ifl b b.formula_struc_base
                 | [(parts2,fl2,f2)] ->
                       let sf2 = rec_pre parts2 fl2 b f2 in
                       let () =  Debug.ninfo_hprint (add_str "sf2" (Cprinter.string_of_struc_formula)) sf2 no_pos in
                       sf2
                 | _ -> (* case here *)
                       let case_sfs = List.map (fun (parts2,fl2,f2) ->
                           let sf2 = CF.EBase {b with CF.formula_struc_base = f2;} in
                           let n_parts = if CF.equal_flow_interval fl2 !norm_flow_int then parts else parts2 in
                           let sf3 = recf n_parts fl2 sf2 in
                           let old_baga_flag = !baga_xpure in
                           let () = baga_xpure := true in
                           let guard,_,_=(x_add Cvutil.xpure_symbolic 11 prog f2) in
                           let () = baga_xpure := old_baga_flag in
                           let p_guard = CP.remove_redundant (MCP.pure_of_mix guard) in
                           let sf4 = elim_dup_with_guard p_guard sf3 in
                           (p_guard, sf4)
                       ) pr_fl_fs in
                       let n_sf = CF.ECase { CF.formula_case_branches = case_sfs;
                       formula_case_pos = b.CF.formula_struc_pos;
                       } in
                       let () =  Debug.ninfo_hprint (add_str " f1" (Cprinter.string_of_formula))  f1 no_pos in
                       let () =  Debug.ninfo_hprint (add_str " n_sf" (Cprinter.string_of_struc_formula)) n_sf no_pos in
                       let sf4 = if CF.isConstTrueFormula f1 then n_sf
                       else CF.EBase {b with
                           CF.formula_struc_continuation = Some n_sf;
                           CF.formula_struc_implicit_inst =  CP.remove_dups_svl (b.CF.formula_struc_implicit_inst@(CF.fresh_data_v_no_change  f1));
                           CF.formula_struc_base = f1;}
                       in
                       sf4
             end
          | [] ->
                let f2 = formula_fct b.formula_struc_base in
                rec_pre parts ifl b f2
          | _ -> struc_fnc sf
      end
    | CF.EAssume ea->
          let () =  Debug.ninfo_hprint (add_str " ea.CF.formula_assume_simpl" (Cprinter.string_of_formula))  ea.CF.formula_assume_simpl no_pos in
          let () =  Debug.ninfo_hprint (add_str " ifl post" (string_of_flow)) ifl no_pos in
          let l_hpdefs = List.fold_left (fun r (fl1,defs) ->
              if CF.equal_flow_interval fl1 ifl then
              r@defs
              else r
          ) [] parts in
          let f1 = formula_subst_dangling_pred_post dang_hps to_unfold_hps post_hps l_hpdefs ifl ea.CF.formula_assume_simpl in
          let () =  Debug.ninfo_hprint (add_str "f1" (Cprinter.string_of_formula)) f1 no_pos in
          let quans = CF.fresh_data_v_no_change f1 in
          CF.EAssume {ea with CF.formula_assume_simpl = CF.add_quantifiers quans f1;
              CF.formula_assume_struc = (recf parts ifl) ea.CF.formula_assume_struc}
    | CF.EInfer b -> CF.EInfer {b with CF.formula_inf_continuation = (recf parts ifl) b.CF.formula_inf_continuation}
    | CF.EList l -> CF.EList (Gen.map_l_snd (recf parts ifl) l)
  in
  (***************************************************)
  let () =  Debug.ninfo_hprint (add_str "sf" (Cprinter.string_of_struc_formula)) sf no_pos in
  (* partition hpdefs into sets of defs based on flows *)
  (* for each one,
     - bottom up
     - construct case based on duplicate
     - find defs
  *)
  let part_defs = flow_partition hpdefs [] in
  (* let nf_defs,rem = partition_nf part_defs [] in *)
  if List.length part_defs <= 1 then struc_fnc sf
  else
    gen_case_spec part_defs !norm_flow_int sf

let case_struc_formula_trans prog dang_hps to_unfold_hps pre_hps post_hps hpdefs struc_fnc fct f =
  let pr = !CF.print_struc_formula in
  Debug.no_4 "case_struc_formula_trans" !CP.print_svl !CP.print_svl !CP.print_svl pr pr
      (fun _ _ _ _ -> case_struc_formula_trans_x prog dang_hps to_unfold_hps pre_hps post_hps hpdefs struc_fnc fct f)
      to_unfold_hps pre_hps post_hps f


let trans_specs_hprel_2_cview iprog cprog proc_name unk_hps
      to_unfold_hps pre_hps post_hps hpdefs chprels_decl =
  let view_equivs = cprog.C.prog_view_equiv in
  let sel_view_equivs = List.fold_left (fun r hpdcl ->
      try
        let equiv_view = List.assoc hpdcl.C.hp_name view_equivs in
        r@[(hpdcl.C.hp_name,equiv_view)]
      with _ -> r
  ) [] chprels_decl in
  let rec get_sst_hp hp_defs res=
    match hp_defs with
      | [] -> res
      | hp_def::rest -> begin
          let rec_fnc = get_sst_hp rest res in
          match hp_def.CF.def_cat with
            | Cpure.HPRelDefn (hp,r,args) -> begin
                let fs = List.fold_left (fun r (f,_) -> r@(CF.list_of_disjs f) ) [] hp_def.CF.def_rhs in
                match fs with
                  | [f] -> begin
                      try
                        let hpargs = CF.extract_HRel_f f in
                        let hpargs0 = CF.extract_HRel  hp_def.CF.def_lhs in
                        get_sst_hp rest (res@[(hpargs0, hpargs)])
                      with _ -> rec_fnc
                    end
                  | _ -> rec_fnc
              end
            | _ -> rec_fnc
        end
  in
  let hn_hprel_subst_trans sst_hps hn = match hn with
    | CF.HRel (hp, eargs,p) -> begin
       try
         let ((hp1,frm_args1),(hp2,frm_args2)) = List.find (fun ((hp1,_),_) -> CP.eq_spec_var hp hp1) sst_hps in
         let to_args1 = List.concat (List.map CP.afv eargs) in
         let sst0 = List.combine frm_args1 to_args1 in
         let to_args2 = CP.subst_var_list sst0 frm_args2 in
         let eargs2 = List.map (fun sv -> CP.mkVar sv no_pos) to_args2 in
         CF.HRel (hp2, eargs2, p)
       with _ -> hn
      end
    | _ -> hn
  in
  (* let fresh_data_v f= *)
  (*  let quans, f0 = CF.split_quantifiers f in *)
  (*  let hds, hvs, hrs = CF.get_hp_rel_formula f0 in *)
  (*  let v_sps1 = List.fold_left (fun r hd -> r@(List.filter (fun sv -> not (CP.is_node_typ sv)) hd.CF.h_formula_data_arguments)) [] hds in *)
  (*  let v_sps2 = List.fold_left (fun r hd -> r@(List.filter (fun sv -> not (CP.is_node_typ sv)) hd.CF.h_formula_view_arguments)) v_sps1 hvs in *)
  (*  let fr_v_sps2 = CP.diff_svl (CP.remove_dups_svl v_sps2) quans in *)
  (*  CF.add_quantifiers (quans@fr_v_sps2) f0 *)
  (* in *)
  let formula_subst_dangling_pred dang_hps to_unfold_hps post_hps hpdefs f0=
    let () =  Debug.ninfo_hprint (add_str "f0" (Cprinter.string_of_formula)) f0 no_pos in
    (* let () =  print_endline ("f0: " ^ (Cprinter.string_of_formula f0))  in *)
    let () =  Debug.ninfo_hprint (add_str "dang_hps" (!CP.print_svl)) dang_hps no_pos in
    let () =  Debug.ninfo_hprint (add_str "post_hps" (!CP.print_svl)) post_hps no_pos in
    let () =  Debug.ninfo_hprint (add_str " to_unfold_hps" (!CP.print_svl))  to_unfold_hps no_pos in
    (* let () =  print_endline (" to_unfold_hps : " ^ (!CP.print_svl  to_unfold_hps)) in *)
    (* let hp_opt = CF.extract_hrel_head_w_args f0 in *)
    let hp_opt = CF. extract_hprel_pure f0 in
    match hp_opt with
      | None -> f0
      | Some (hp,args,p) -> let pos = (CF.pos_of_formula f0) in
        if CP.mem_svl hp dang_hps then CF.formula_of_pure_N  p (* CF.mkTrue_nf *) pos
        else
          if CP.mem_svl hp to_unfold_hps then
            try
              let hp_def = CF.look_up_hp_def hpdefs hp in
              let f1 = CF.disj_of_list (List.map fst hp_def.CF.def_rhs) no_pos in
              let _,fm_args = CF.extract_HRel hp_def.CF.def_lhs in
              let ss = List.combine fm_args args in
              let f2 =  (CF.subst ss f1) in
              let f3= (* if CP.mem_svl hp post_hps then fresh_data_v f2 else *) f2 in
              let p2 = CP.subst ss p in
              let f4 = CF. mkAnd_pure f3 (MCP.mix_of_pure p2) pos in
              let f5,ls_equans = CF.drop_hrel_f f4 dang_hps in
              (* let quans = (List.fold_left List.append [] (List.map CP.afv (List.concat ls_equans))) in *)
              (* let f6 = CF.add_quantifiers quans f5 in *)
              let () =  Debug.ninfo_hprint (add_str "f5" (Cprinter.string_of_formula)) f5 no_pos in
              (* let () =  print_endline ("f6: " ^ (Cprinter.string_of_formula f6))  in *)
              f5
            with _ -> f0
          else
            f0
  in
  let update_infer_objs sf=
    match sf with
        | CF.EInfer ei ->
              let inf_obj = ei.CF.formula_inf_obj in
              if inf_obj # is_pre || inf_obj # is_post || inf_obj # is_term then
                let new_inf_obj = inf_obj # clone in
                let _ = new_inf_obj # reset INF_SHAPE in
                let new_inf_vars = List.filter (fun sv -> not (Cpure.is_hprel_typ sv)) ei.CF.formula_inf_vars in
                CF.EInfer {ei with
                    CF.formula_inf_obj = new_inf_obj;
                    CF.formula_inf_continuation = sf;
                    CF.formula_inf_vars = new_inf_vars
                }
              else sf
        | _ -> sf
  in
  (*****************END INTERNAL*****************)
  let sst_hps = get_sst_hp hpdefs [] in
  let plug_views_proc proc =
    let _ =  Debug.ninfo_hprint (add_str "proc.C.proc_static_specs" (
      let pr proc = Cprinter.string_of_struc_formula_for_spec (proc.C.proc_static_specs) in
      pr)) proc no_pos in
    let _ =  Debug.ninfo_hprint (add_str "plug_views_proc" (
      let pr proc = Cprinter.string_of_struc_formula_for_spec (proc.Cast.proc_stk_of_static_specs # top) in
      pr)) proc no_pos in
    if proc.C.proc_hpdefs = [] then proc else
      let formula_fnc= (formula_subst_dangling_pred unk_hps to_unfold_hps (CP.remove_dups_svl (proc.C.proc_sel_post_hps@post_hps)) hpdefs) in
      let trans_struc_formula_fn = if !Globals.sae then
        (case_struc_formula_trans cprog unk_hps to_unfold_hps pre_hps (CP.remove_dups_svl (proc.C.proc_sel_post_hps@post_hps)) hpdefs (CF.struc_formula_trans_heap_node [] formula_fnc)) formula_fnc
      else CF.struc_formula_trans_heap_node [] formula_fnc
      in
      let name = C.unmingle_name proc.C.proc_name in
      (* let () = print_endline ("proc_name: "^name) in *)
      let s_spec1 = (CF.struc_formula_drop_infer unk_hps proc.C.proc_static_specs) in
      (*subst simple view def (equiv, should subst views with one branch also)*)
      let () =  Debug.ninfo_hprint (add_str "to_unfold_hps" (!CP.print_svl)) to_unfold_hps no_pos in
      let s_spec2 = if unk_hps=[] && to_unfold_hps=[] then s_spec1 else
        (* let to_unfold_vnames = List.map (CP.name_of_spec_var) to_unfold_hps in *)
        (* CF.struc_formula_trans_heap_node *)
        trans_struc_formula_fn s_spec1
      in
      let () =  Debug.ninfo_hprint (add_str "s_spec2" (Cprinter.string_of_struc_formula)) s_spec2 no_pos in
      let s_spec3 = if sst_hps = [] then s_spec2 else
        CF.struc_formula_trans_heap_node [] (CF.formula_map (hn_hprel_subst_trans sst_hps)) s_spec2
      in
      let hn_trans_formula = trans_formula_hp_2_view iprog cprog name chprels_decl proc.C.proc_hpdefs sel_view_equivs in
      let n_static_spec = CF.struc_formula_trans_heap_node [] hn_trans_formula s_spec3 in
      let () =  Debug.ninfo_hprint (add_str "trans static spec" (Cprinter.string_of_struc_formula)) n_static_spec no_pos in
      (* stack specs *)
      let stk_spec1= (CF.struc_formula_drop_infer unk_hps proc.C.proc_stk_of_static_specs # top) in
      let _ =  Debug.ninfo_hprint (add_str "stk_spec1" (Cprinter.string_of_struc_formula)) (stk_spec1) no_pos in
      let stk_spec2 =  if unk_hps=[] && to_unfold_hps=[] then stk_spec1 else
        trans_struc_formula_fn stk_spec1
      in
      let _ =  Debug.ninfo_hprint (add_str "stk_spec2" (Cprinter.string_of_struc_formula)) (stk_spec2) no_pos in
      let stk_spec3 = if sst_hps = [] then stk_spec2 else
        CF.struc_formula_trans_heap_node [] (CF.formula_map (hn_hprel_subst_trans sst_hps)) stk_spec2
      in
      let _ =  Debug.ninfo_hprint (add_str "stk_spec3" (Cprinter.string_of_struc_formula)) (stk_spec3) no_pos in
      let n_stk_spec = CF.struc_formula_trans_heap_node [] hn_trans_formula stk_spec3 in
      let _ =  Debug.ninfo_hprint (add_str "n_stk_spec" (Cprinter.string_of_struc_formula)) n_stk_spec no_pos in
      let n_dynamic_spec = CF.struc_formula_trans_heap_node [] hn_trans_formula (CF.struc_formula_drop_infer unk_hps proc.C.proc_dynamic_specs) in
      let n_static_spec = match proc.C.proc_static_specs with
        | CF.EInfer ei ->
              let inf_obj = ei.CF.formula_inf_obj in
              if inf_obj # is_pre || inf_obj # is_post || inf_obj # is_term then
                let new_inf_obj = inf_obj # clone in
                let () = new_inf_obj # reset INF_SHAPE in
                let new_inf_vars = List.filter (fun sv -> not (Cpure.is_hprel_typ sv)) ei.CF.formula_inf_vars in
                CF.EInfer {ei with
                    CF.formula_inf_obj = new_inf_obj;
                    CF.formula_inf_continuation = n_static_spec;
                    CF.formula_inf_vars = new_inf_vars
                }
              else n_static_spec
        | _ -> n_static_spec
      in
      let n_dynamic_spec = match proc.C.proc_dynamic_specs with
        | CF.EInfer ei ->
              let inf_obj = ei.CF.formula_inf_obj in
              if inf_obj # is_pre || inf_obj # is_post || inf_obj # is_term then
                let new_inf_obj = inf_obj # clone in
                let () = new_inf_obj # reset INF_SHAPE in
                let new_inf_vars = List.filter (fun sv -> not (Cpure.is_hprel_typ sv)) ei.CF.formula_inf_vars in
                CF.EInfer {ei with
                    CF.formula_inf_obj = new_inf_obj;
                    CF.formula_inf_continuation = n_dynamic_spec;
                    CF.formula_inf_vars = new_inf_vars
                }
              else n_dynamic_spec
        | _ -> n_dynamic_spec
      in
      let n_stk_spec = update_infer_objs n_stk_spec in
      let n_stk_specs = proc.C.proc_stk_of_static_specs in
      let _ = n_stk_specs # pop in
      let _ =  n_stk_specs # push n_stk_spec in
      (* let proc_stk_of_static_specs = proc.C.proc_stk_of_static_specs  in *)
      (* let n_proc_stk_of_static_specs = List.map (fun s -> *)
      (*     CF.struc_formula_trans_heap_node [] hn_trans_formula (CF.struc_formula_drop_infer unk_hps s) *)
      (* ) proc_stk_of_static_specs # get_stk in *)
      (* let () = proc_stk_of_static_specs # reset in *)
      (* let () = proc_stk_of_static_specs # push_list n_proc_stk_of_static_specs in *)
      let proc1 = { proc with C.proc_static_specs= n_static_spec;
          C.proc_dynamic_specs= n_dynamic_spec;
          C.proc_stk_of_static_specs =  n_stk_specs;
      }
      in
      let res = Astsimp.add_pre_to_cprog_one cprog proc1 in
      let _ =  Debug.ninfo_hprint (add_str "stk_spec ENDING" (Cprinter.string_of_struc_formula)) (proc1.C.proc_stk_of_static_specs #top) no_pos in
      res
  in
  (* let () = print_endline ("unk_hps: "^ (!CP.print_svl unk_hps)) in *)
  let old_procs = cprog.C.new_proc_decls in
  let proc_decls = Hashtbl.fold (fun i p acc ->
      let np = if String.compare p.C.proc_name proc_name == 0 then
      plug_views_proc p
      else p
      in
      acc@[(i,np)]
  ) old_procs [] in
  let () = Hashtbl.reset old_procs in
  let () = List.iter (fun (i,p) -> Hashtbl.add old_procs i p) proc_decls in
  {cprog with
      C.new_proc_decls = old_procs;
  }
(*******************************)
(********END REVERIFY**********)
(*******************************)

let plug_shape_into_specs_x cprog iprog dang_hps proc_names pre_hps post_hps hp_defs=
  (*subst simple precondition*)
  let need_trans_hprels0, unk_hps, simpl_hps =
    List.fold_left (fun (r_hp_defs, r_unk_hps, r_simp_hps) hp_def ->
        match hp_def.CF.def_cat with
          |  Cpure.HPRelDefn (hp,r,args) -> begin
               let f = CF.disj_of_list (List.map fst hp_def.CF.def_rhs) no_pos in
               let simp_hps = if not (CF.is_disj f) then r_simp_hps@[hp] else r_simp_hps in
               try
                 let todo_unk = x_add Cast.look_up_view_def_raw 33 cprog.Cast.prog_view_decls
                   (Cpure.name_of_spec_var hp)
                 in
                 (r_hp_defs, r_unk_hps, simp_hps)
               with Not_found ->
                   (*at least one is node typ*)
                   if List.exists (fun sv -> Cpure.is_node_typ sv) (r::args) then
                     if (Cformula.is_unknown_f f) then
                       r_hp_defs, r_unk_hps@[hp], r_simp_hps
                     else r_hp_defs@[hp_def], r_unk_hps, simp_hps
                   else r_hp_defs, r_unk_hps, simp_hps
             end
          | _ -> (r_hp_defs, r_unk_hps, r_simp_hps)
    ) ([],[],[]) hp_defs in
  let unk_hps = CP.remove_dups_svl (dang_hps@unk_hps) in
  let () = Debug.ninfo_hprint (add_str "    unk_hps" (!CP.print_svl))  unk_hps no_pos in
  let plug_proc need_trans_hprels1 chprels_decl cprog proc_name=
    let cprog = trans_specs_hprel_2_cview iprog cprog proc_name unk_hps simpl_hps
      pre_hps post_hps need_trans_hprels1 chprels_decl in
    cprog
  in
  let need_trans_hprels1 =(*  List.map (fun (a,b,c,f) -> *)
  (*     let new_f,_ = Cformula.drop_hrel_f f unk_hps in *)
  (*     (a,b,c,new_f) *)
  (* ) *) need_trans_hprels0 in
  try
  let n_cviews,chprels_decl = trans_hprel_2_cview iprog cprog "" need_trans_hprels1 in
  let cprog = List.fold_left (plug_proc need_trans_hprels1 chprels_decl) cprog proc_names in
  cprog
  with _ ->
      let () = print_endline_quiet ("\n --:plug_shape_into_specs warning: "^" at:"^(get_backtrace_quiet ())) in
      cprog

let plug_shape_into_specs cprog iprog dang_hps proc_names pre_hps post_hps hp_defs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 =String.concat ";" in
  Debug.no_4 "plug_shape_into_specs" !CP.print_svl !CP.print_svl pr1 pr2 pr_none
      (fun _ _ _ _ -> plug_shape_into_specs_x cprog iprog dang_hps proc_names pre_hps post_hps hp_defs)
      pre_hps post_hps hp_defs proc_names


let () = Solver.trans_hprel_2_cview := trans_hprel_2_cview;;
let () = Solver.trans_formula_hp_2_view := trans_formula_hp_2_view;;
