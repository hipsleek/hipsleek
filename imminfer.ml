(**
Created 12-June-2015
Program transformations related to immutability annotations inference.
**)

#include "xdebug.cppo"
open VarGen
open Globals
open Gen

module C = Cast
module CF = Cformula
module CP = Cpure
module I = Iast

let fresh_pred loc = fresh_any_name rel_default_prefix_name
let fresh loc = fresh_any_name imm_var_prefix
let fresh_ann loc = CP.SpecVar (AnnT, fresh loc, Unprimed)

let should_infer_imm_pre = ref false
let should_infer_imm_post = ref false
let is_infer = ref false

let infer_imm_ann_proc (proc_static_specs: CF.struc_formula) : (CF.struc_formula * C.rel_decl option * C.rel_decl option) =
  let open Cformula in
  (* Will be set to false later when @imm_pre or @imm_post is set *)
  let use_mutable = ref true in
  let imm_post_is_set = ref false in
  let imm_pre_is_set = ref false in
  (* Stack of added fresh variables in both pre && post *)
  let post_stack = new Gen.stack in
  let n_stack = new Gen.stack in
  (* Stack of added fresh variables in both pre *)
  let pre_stack = new Gen.stack in
  (* Stack of added constant anot normalization *)
  let pre_norm_stack = new Gen.stack in
  (* Relation added on pre and post *)
  let pre_rel = ref None in
  let post_rel = ref None in
  let pre_intro = ref CP.SetSV.empty in
  let assign_ann_or_var ann loc = match ann with
    | CP.NoAnn -> (let f = fresh_ann loc
                   in (CP.PolyAnn f, Some (f, false)))
    | CP.ConstAnn _ -> if (not !Globals.allow_imm_norm) then (ann, None)
                       else (let f = fresh_ann loc in (ann, Some (f, true)))
    | CP.PolyAnn f -> (ann, Some (f, false))
    | ann -> (ann, None) in
  let update_pre_stack v = map_opt_def () (fun (v,_) -> pre_stack # push v) v in
  let update_post_stack v = map_opt_def () (fun (v,_) -> post_stack # push v) v in
  let update_n_stack v ann =
    map_opt_def () (fun (v,norm) -> if norm then n_stack # push (v, ann)) v in
  let update_pre_intro ann v =
    match ann, v with
    | CP.NoAnn, Some (sv,_) -> pre_intro := CP.SetSV.add sv !pre_intro
    | CP.ConstAnn _, Some (sv,_) -> pre_intro := CP.SetSV.add sv !pre_intro
    | _ -> () in
  let ann_heap_ho is_post loc imm_ann imm_ann_params =
    let update_heap_imm imm_ann =
      let (h_imm, v) = assign_ann_or_var imm_ann loc in
      let () = if is_post then () else update_pre_intro imm_ann v in
      let () = (if is_post then update_post_stack else update_pre_stack) v in
      let () = update_n_stack v h_imm in
      let h_imm = match v with
        | Some (_, false) -> h_imm
        | Some (v, true) -> CP.PolyAnn v
        | None -> h_imm in
      h_imm in
    let result = (update_heap_imm imm_ann, List.map update_heap_imm imm_ann_params) in
    result in
  let ann_heap is_post h = match h with
    | DataNode hp ->
       let (h_imm, h_imm_params) =
         ann_heap_ho is_post hp.h_formula_data_pos hp.h_formula_data_imm
                     hp.h_formula_data_param_imm in
       Some (DataNode { hp with h_formula_data_imm = h_imm;
                                h_formula_data_param_imm = h_imm_params })
    | ViewNode hp ->
       let (h_imm, _) =
         ann_heap_ho is_post hp.h_formula_view_pos hp.h_formula_view_imm [] in
       Some (ViewNode { hp with h_formula_view_imm = h_imm })
    | _ -> None
  in
  let and_pure_with_eqs vars formula loc =
    let eq_v (v, ann) =
      match ann with
      | CP.ConstAnn h_ann ->
         let p_formula = CP.Eq (CP.Var (v,loc), CP.AConst (h_ann, loc), loc) in
         let b_formula = (p_formula, None) in
         CP.BForm (b_formula, None)
      | _ -> failwith "Not possible"
    in
    List.fold_right (fun pure acc -> add_pure_formula_to_formula pure acc) (List.map eq_v vars) formula in
  let and_pure_with_rel relname rel_params formula loc =
    let rel_pure =
      let pairs = List.map (fun sv -> (CP.type_of_spec_var sv, CP.Var (sv, loc)))
                           rel_params in
      let (types, args) = List.split pairs in
      let rel_sv = CP.SpecVar (RelT types, relname, Unprimed) in
      let p_formula = CP.RelForm (rel_sv, args, loc) in
      let rel = CP.mkPure p_formula in 
      rel
    in add_pure_formula_to_formula rel_pure formula in
  let and_pure_with_rel relname rel_params formula loc =
    Debug.no_3 "and_pure_with_rel" pr_id !CP.print_svl !CF.print_formula !CF.print_formula (fun _ _ _ -> and_pure_with_rel relname rel_params formula loc) relname rel_params formula in
  let mk_rel rel_params loc =
    let rn = fresh_pred loc in
    match rel_params with
    | [] -> None
    | rel_params ->
       Some ({
        C.rel_name = rn;
        C.rel_vars = List.map (fun sv -> CP.SpecVar (CP.type_of_spec_var sv,
                                                     fresh loc, Unprimed)) rel_params;
        C.rel_formula = CP.mkTrue no_pos
       })
  in
  let rec ann_struc_formula_1 = function
    | EInfer ff ->
       is_infer := true;
       imm_pre_is_set := ff.formula_inf_obj # is_pre_imm && !should_infer_imm_pre;
       should_infer_imm_pre := !imm_pre_is_set;
       x_tinfo_hp (add_str "!should_infer_imm_pre" string_of_bool) !should_infer_imm_pre no_pos;
       (* has_infer_imm_pre := (!has_infer_imm_pre || !imm_pre_is_set) && !should_infer_imm_pre; *)
       imm_post_is_set := ff.formula_inf_obj # is_post_imm;
       should_infer_imm_post := !imm_post_is_set && (not(!imm_pre_is_set) || !should_infer_imm_post);
       (* has_infer_imm_post := (!has_infer_imm_post || !imm_post_is_set) && !should_infer_imm_post; *)
       x_ninfo_hp (add_str "imm_pre_flag" string_of_bool) !imm_pre_is_set no_pos;
       x_ninfo_hp (add_str "imm_post_flag" string_of_bool) !imm_post_is_set no_pos;
       use_mutable := (not !imm_pre_is_set && not !imm_post_is_set);
       None
    | EAssume ff ->
      let new_formula = transform_formula (transform_1 true) ff.formula_assume_simpl in
      Some (EAssume { ff with formula_assume_simpl = new_formula;
                              formula_assume_struc = CF.formula_to_struc_formula new_formula })
    | _ -> None
  and transform_1 is_post =
    (ann_struc_formula_1, nonef, ann_heap is_post, (somef, somef, somef, somef, somef)) in
  let ann_postcondition = function
    | EAssume ff ->
       let loc = pos_of_formula ff.formula_assume_simpl in
       (* Normalize postcondition *)
       let postcondition =
         if (not (n_stack # is_empty)) then
           and_pure_with_eqs (n_stack # get_stk) ff.formula_assume_simpl loc
         else ff.formula_assume_simpl in
       let postcondition_add_qvars =
         CF.push_exists (post_stack # get_stk) postcondition in
       (* And the pure part with relation *)
       if ((not (post_stack # is_empty)) && (not (!post_rel = None)) && !should_infer_imm_post) then
         let post_rel = match !post_rel with Some p -> p | None -> failwith "Not possible (infer_imm_ann_proc)" in
         let rel_params = (* (pre_stack # get_stk) @ *) (post_stack # get_stk) in
         let postcondition_with_rel = and_pure_with_rel post_rel.C.rel_name rel_params
                                                        postcondition_add_qvars loc in
         Some (EAssume { ff with formula_assume_simpl = postcondition_with_rel;
                                 formula_assume_struc = CF.formula_to_struc_formula postcondition_with_rel })
       else Some (EAssume {ff with formula_assume_simpl = postcondition_add_qvars;
                                   formula_assume_struc = CF.formula_to_struc_formula
                                                            postcondition_add_qvars })
    | _ -> None
  in
  let ann_struc_formula_2 = function
    | EInfer ff ->
       is_infer := true;
       begin
         match ff.formula_inf_continuation with
         | EBase ({ formula_struc_base = precondition; formula_struc_pos = loc; formula_struc_implicit_inst = impl_inst } as ebase) ->
            let ebase = { ebase with
                          formula_struc_implicit_inst = Gen.BList.remove_dups_eq CP.eq_spec_var
                                                        ((CP.SetSV.elements !pre_intro) @ impl_inst) } in
            let new_ebase =
              (* Normalize precondition *)
              let precondition =
                if (not (pre_norm_stack # is_empty)) then
                  and_pure_with_eqs (pre_norm_stack # get_stk) precondition loc
                else precondition in
              if (not (pre_stack # is_empty) && not (!pre_rel = None)) then
                let pre_rel = match !pre_rel with Some p -> p | None -> failwith "Not possible (infer_imm_ann_proc)" in
                let rel_params = pre_stack # get_stk in
                let precondition_with_rel = if (!should_infer_imm_pre) then and_pure_with_rel pre_rel.C.rel_name rel_params precondition loc else precondition in 
                { ebase with formula_struc_base = precondition_with_rel }
              else { ebase with formula_struc_base = precondition } in
            let new_continuation =
              if (not (post_stack # is_empty)) then
                let transform = (ann_postcondition, nonef, nonef, (nonef, nonef, nonef, nonef, nonef)) in
                let base_continuation = map_opt (transform_struc_formula transform) ebase.formula_struc_continuation in
                EBase { new_ebase with formula_struc_continuation = base_continuation }
              else EBase new_ebase in
            let new_inf_vars =
              let rel_to_var rel en = if not(en) then [] else 
                  match rel with
                  (* the relation var *)
                  | Some p -> [CP.SpecVar (RelT (CP.type_of_spec_var_list  p.C.rel_vars), p.C.rel_name, Unprimed)]
                  | None -> [] in
              (rel_to_var !post_rel !should_infer_imm_post)@(rel_to_var !pre_rel !should_infer_imm_pre)@ff.formula_inf_vars in
            Some (EInfer { ff with formula_inf_continuation = new_continuation;
                                   formula_inf_vars = new_inf_vars })
         | _ -> None
       end
    | other -> Some other
  in
  let transform_2 = (ann_struc_formula_2, somef, somef, (somef, somef, somef, somef, somef)) in
  let pss =
    let pss_1 = transform_struc_formula (transform_1 false) proc_static_specs in
    (pre_norm_stack # push_list (n_stack # get_stk_and_reset);
     if (!imm_pre_is_set && !should_infer_imm_pre) then pre_rel := mk_rel (pre_stack # get_stk) no_pos;
     if (!imm_post_is_set && !should_infer_imm_post) then post_rel :=
                                mk_rel ((* (pre_stack # get_stk)@ *)(post_stack # get_stk)) no_pos;
     transform_struc_formula transform_2 pss_1) in
  (pss, !pre_rel, !post_rel)

let pr_infer_imm_ann_result (f, r1, r2) =
  let open Cprinter in
  fmt_open_vbox 0;
  pr_add_str_cut "cformula:" pr_struc_formula f;
  pr_add_str_cut "pre_rel:" fmt_string
    (map_opt_def "None" (fun x -> x.C.rel_name) r1);
  pr_add_str_cut "post_rel:" fmt_string
    (map_opt_def "None" (fun x -> x.C.rel_name) r2);
  fmt_close ()

let infer_imm_ann_proc (proc_static_specs: CF.struc_formula) : (CF.struc_formula * C.rel_decl option * C.rel_decl option) =
  Debug.no_1 "infer_imm_ann_proc" Cprinter.string_of_struc_formula
              (Cprinter.poly_string_of_pr_gen 0 pr_infer_imm_ann_result) infer_imm_ann_proc
             proc_static_specs

let update_rel_tables prog rel_list =
  let update_smtrel  rel_decl = Smtsolver.add_relation rel_decl.Cast.rel_name rel_decl.Cast.rel_vars rel_decl.Cast.rel_formula in
  let () = List.iter update_smtrel rel_list in 
  let () = prog.C.prog_rel_decls # push_list_pr x_loc rel_list in 
  prog

let infer_imm_ann (prog: C.prog_decl) (proc_decls: C.proc_decl list) : C.prog_decl * C.proc_decl list =
  (** Infer immutability annotation variables for one proc,
      @return (new proc, precondition relation, postcondition relation) **)
  (* let pre = false in  *)
  let (new_proc_decls, rel_list) =
    let helper proc (proc_decls, rel_list) =
      let old_specs = proc.C.proc_stk_of_static_specs # pop_top in
      let (pre_rels, post_rels,pss) = (* List.fold_right (fun spec (pre_rels, post_rels) -> *)
        let (pss, pre_rel, post_rel) = x_add_1 infer_imm_ann_proc old_specs in
        let pre_rels = map_opt_def []  (fun r -> [r]) pre_rel in
        let post_rels = map_opt_def [] (fun r -> [r]) post_rel in
        proc.C.proc_stk_of_static_specs # push_pr x_loc pss;
        (* pss_stk # push pss; *)
        (pre_rels, post_rels, pss)(* ) old_specs ([], []) *)
      in
      (* (({proc with C.proc_stk_of_static_specs = proc.C.proc_stk_of_static_specs; C.proc_static_specs = pss }) *)
      (proc::proc_decls, pre_rels@post_rels@rel_list) in
    List.fold_right helper proc_decls ([], []) in
  let prog = update_rel_tables prog rel_list in
  (prog, new_proc_decls)

let infer_imm_ann (prog: C.prog_decl) (proc_decls: C.proc_decl list) : C.prog_decl * C.proc_decl list  =
  let pr = pr_list (fun p -> Cprinter.string_of_struc_formula (p.C.proc_stk_of_static_specs # top) (* p.Cast.proc_static_specs *)) in
  let pr_out (_,b) = 
      (pr_list (add_str "proc_decls" (fun p -> Cprinter.string_of_struc_formula (p.C.proc_stk_of_static_specs # top) (* p.Cast.proc_static_specs *)))) b
  in
  Debug.no_1 "infer_imm" pr pr_out (fun _ -> infer_imm_ann prog proc_decls) proc_decls 

let infer_imm_ann_prog (prog: C.prog_decl) : C.prog_decl =
  let proc_decls = Hashtbl.create (Hashtbl.length prog.C.new_proc_decls) in
  let (new_proc_decls, rel_list) =
    let helper id proc (proc_decls, rel_list) =
      let pss_stk = new Gen.stack_pr "pss_stk" Cprinter.string_of_struc_formula (==) in
      let old_specs = proc.C.proc_stk_of_static_specs # get_stk in
      let (pre_rels, post_rels) = List.fold_right (fun spec (pre_rels, post_rels) ->
        let (pss, pre_rel, post_rel) = x_add_1 infer_imm_ann_proc spec in
        let pre_rels = map_opt_def pre_rels (fun r -> r::pre_rels) pre_rel in
        let post_rels = map_opt_def post_rels (fun r -> r::post_rels) post_rel in
        pss_stk # push_pr x_loc pss;
        (pre_rels, post_rels)) old_specs ([], []) in
      ((id, { proc with C.proc_stk_of_static_specs = pss_stk;
                     (* C.proc_static_specs = (pss_stk # top) *) })::proc_decls, pre_rels@post_rels@rel_list) in
    Hashtbl.fold helper prog.new_proc_decls ([], []) in
  let prog = update_rel_tables prog rel_list in
  List.iter (fun (id, proc_decl) -> Hashtbl.add proc_decls id proc_decl) new_proc_decls;
  { prog with C.new_proc_decls = proc_decls }

let should_infer_imm prog inf_vars inf_obj =
  let arg_is_ann id =
    try
      let rel_decl = I.look_up_rel_def_raw prog.I.prog_rel_decls id in
      List.fold_right (fun (x,_) acc -> (Ipure.is_ann_type x) && acc)
                      rel_decl.I.rel_typed_vars
                      true
    with _ -> false
  in
  let has_imm_rel = List.fold_right (fun (id,_) acc -> (arg_is_ann id) || acc) inf_vars false in
  inf_obj # is_pre_imm ||  inf_obj # is_post_imm || !Globals.allow_noann || has_imm_rel

(* collects the guard reloblgs. eg, for P(a:AnnT,b:AnnT) ~> a<:@A & b<:@A -> P(a,b) *)
let collect_reloblgs_spec (spec: CF.struc_formula) =
  let infer_rel_stk = new Gen.stack in
  let collect_reloblgs_b (p_formula, _) =
    match p_formula with
    | CP.RelForm (rel_sv, args, _) ->
       let () = x_ninfo_hp (add_str "args" Cprinter.string_of_typed_spec_var_list)
                           (List.map CP.exp_to_spec_var args) no_pos in
       let guards = List.fold_right (fun exp guards -> 
                                      if CP.is_ann_typ (CP.exp_to_spec_var exp) then
                                        (CP.mkSubAnn exp CP.const_ann_top)::guards
                                      else guards) args [] in
       let () = x_ninfo_hp (add_str "guards" (pr_list Cprinter.string_of_pure_formula)) guards no_pos in
       let reloblg = CP.RelAssume [rel_sv], CP.mkPure p_formula,
                     (CP.join_conjunctions guards) in
       let () = if guards != [] then infer_rel_stk # push reloblg in
       None
    | _ -> None
  in
  let collect_reloblgs = (nonef, nonef, nonef, (nonef, nonef, nonef,
                                                collect_reloblgs_b, nonef)) in
  ignore (CF.transform_struc_formula collect_reloblgs spec);
  (infer_rel_stk # get_stk)

let collect_reloblgs_proc (proc : C.proc_decl) =
  let specs = proc.C.proc_stk_of_static_specs # get_stk in
  List.concat (List.map collect_reloblgs_spec specs)

let collect_reloblgs (proc_decls: C.proc_decl list) =
  List.concat (List.map collect_reloblgs_proc proc_decls)

let wrapper_infer_imm_pre_post_seq infer_stk verify_scc prog verified_scc scc =
  let _ = is_infer := false in
  let _ = should_infer_imm_pre := true in
  let _ = should_infer_imm_post := false in
  let helper prog scc = 
    let prog, scc = x_add infer_imm_ann prog scc in
    let _ = x_tinfo_pp "imm infer start" no_pos in
    let reloblgs = collect_reloblgs scc in
    let () = infer_stk # push_list reloblgs in
    let _ = x_tinfo_pp "imm infer end" no_pos in
    (prog,scc) in
  (* pre-process for pre or post only *)
  let prog, scc1 = helper prog scc in
  let res = verify_scc prog verified_scc scc1 in
  let _ = should_infer_imm_post := not(!should_infer_imm_post) in
  let res = if (!should_infer_imm_pre && !should_infer_imm_post && !is_infer) then 
      (* pre-process for post only *)
      let _ = should_infer_imm_pre := false in
      let prog, vscc = res in
      let scc = List.hd (List.rev vscc) in
      let verified_scc = List.rev (List.tl (List.rev vscc)) in
      let prog0, scc0 = helper prog scc in 
      if !should_infer_imm_post then
        verify_scc prog0 verified_scc scc0
      else res
    else res in
  res 

let wrapper_infer_imm_pre_post_sim infer_stk verify_scc prog verified_scc scc =
  let _ = should_infer_imm_pre := true in
  let _ = should_infer_imm_post := true in
  let helper prog scc = 
    let prog, scc = x_add infer_imm_ann prog scc in
    let _ = x_tinfo_pp "imm infer start" no_pos in
    let reloblgs = collect_reloblgs scc in
    let () = infer_stk # push_list reloblgs in
    let _ = x_tinfo_pp "imm infer end" no_pos in
    prog, scc in
  (* pre-process for pre and post *)
  let prog, scc1 = helper prog scc in
  let res = verify_scc prog verified_scc scc1 in
  res 

let wrapper_infer_imm_pre_post infer_stk verify_scc prog verified_scc scc =
  if not (!Globals.imm_seq) then wrapper_infer_imm_pre_post_sim infer_stk verify_scc prog verified_scc scc
  else wrapper_infer_imm_pre_post_seq infer_stk verify_scc prog verified_scc scc

let wrapper_infer_imm_pre_post infer_stk verify_scc prog verified_scc scc =
 let pr = pr_list (fun p -> Cprinter.string_of_struc_formula (p.C.proc_stk_of_static_specs # top) (* p.Cast.proc_static_specs *)) in
 let pr2 =  (pr_list (pr_list (add_str "proc_decls" (fun p -> Cprinter.string_of_struc_formula (p.C.proc_stk_of_static_specs # top) (* p.Cast.proc_static_specs *))))) in
  let pr_out (a,b) = (pr_pair
    (fun a -> a.Cast.prog_rel_decls # string_of) 
    pr2 )  (a,b)
  in 
  let pr_out (a,b) = pr2 b in
 (* let pr_out = pr_none in *)
 Debug.no_1 "wrapper_infer_imm_pre_post" pr pr_out (fun _ ->  wrapper_infer_imm_pre_post infer_stk verify_scc prog verified_scc scc) scc
