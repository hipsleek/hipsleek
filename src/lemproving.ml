#include "xdebug.cppo"
open VarGen
open Globals
open Wrapper
open Gen
open Others
open Label_only

(* module AS = Astsimp *)
module C  = Cast
module CF = Cformula
module CFU = Cfutil
module CP = Cpure
module H  = Hashtbl
module I  = Iast


let sleek_entail = ref(fun (n: int) (fts:Globals.infer_type list)
  (svl:CP.spec_var list) (cprog:C.prog_decl)
 (cache: (CF.formula * CF.formula) list)
 (ante: CF.formula) (conseq: CF.struc_formula) ->
     let a = (false:bool) in
     let b = (CF.SuccCtx []:CF.list_context) in
     let c = ([]: CP.spec_var list) in
     (a, b, c)
)

(* the cformulae used during lemma proving *)
type lem_formula = 
  | CFormula of CF.formula
  | CSFormula of CF.struc_formula

let lem_to_cformula (lf: lem_formula) = match lf with
  | CFormula f -> f
  | CSFormula csf -> Error.report_error {
      Error.error_loc = no_pos;
      Error.error_text = "cannot have structured formula in antecedent";
    }

let lem_to_struc_cformula (lf: lem_formula) = match lf with
  | CFormula f -> (CF.formula_to_struc_formula f)
  | CSFormula csf -> csf

let string_of_lem_formula lf = match lf with
  | CFormula f -> Cprinter.string_of_formula f
  | CSFormula csf -> Cprinter.string_of_struc_formula csf

let split_infer_vars vrs =
  let p,rl,tl,hp = List.fold_left (fun (p,rl,tl,hp) var -> 
      match var with
      | CP.SpecVar(RelT _,_,_) -> (p,var::rl,tl,hp)
      | CP.SpecVar(FuncT _,_,_) -> (p,rl,var::tl,hp)
      | CP.SpecVar(HpT, _, _ ) -> (p,rl,tl,var::hp)
      | _      -> (var::p,rl,tl,hp)
    ) ([],[],[],[]) vrs in
  (p,rl,tl,hp)

let add_infer_vars_to_ctx ivs ctx =
  let (p,rl,tl,hp) = split_infer_vars ivs in
  let () = Debug.ninfo_hprint (add_str  "rl " !Cpure.print_svl) rl no_pos in
  let ctx = Infer.init_vars ctx p rl tl hp [] in 
  ctx


(* checks if iante(CF.formula) entails iconseq(CF.formula or CF.struc_formula) in cprog(C.prog_decl)
   - similar to Sleekengine.run_entail_check
*)
let run_entail_check_helper ctx (iante: lem_formula) (iconseq: lem_formula) (inf_vars: CP.spec_var list) (cprog: C.prog_decl)  =

  let ante = lem_to_cformula iante in
  let ante = if !Globals.en_slc_ps then Cvutil.prune_preds cprog false ante else ante in
  (* let ante = Solver.prune_preds cprog true ante in (\* (andreeac) redundant? *\) *)
  let conseq = lem_to_struc_cformula iconseq in
  let conseq = if !Globals.en_slc_ps then Cvutil.prune_pred_struc cprog false conseq else conseq in
  (* let conseq = Solver.prune_pred_struc cprog true conseq in (\* (andreeac) redundant ? *\) *)
  (* let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in *)
  (* let ctx = CF.build_context ctx ante no_pos in *)

  let ctx = match ctx with
    | CF.SuccCtx l -> 
      let newl = List.map (fun ct -> 
          let nctx = CF.set_context_formula ct ante in
          let nctx = add_infer_vars_to_ctx inf_vars nctx in
          let nctx = CF.transform_context (x_add Solver.elim_unsat_es 10 cprog (ref 1)) nctx in
          nctx
        ) l in CF.SuccCtx newl
    | CF.FailCtx _ ->    
      Error.report_error {Error.error_loc = no_pos; 
                          Error.error_text = "Cannot Prove Lemma in a False Ctx "}
  in 
  (* let ctx = add_infer_vars_to_list_ctx inf_vars ctx in *)
  (* let () = if !Globals.print_core || !Globals.print_core_all then print_string ("\nrun_entail_check_helper:\n"^(Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") else () in *)
  (* (\* let ctx = CF.transform_list_context (x_add Solver.elim_unsat_es 10 cprog (ref 1)) ctx in *\) *)
  (* let rs1, _ =  *)
  (*   if not !Globals.disable_failure_explaining then *)
  (*     x_add Solver.heap_entail_struc_init_bug_inv cprog false false ctx conseq no_pos None *)
  (*   else *)
  (*     x_add Solver.heap_entail_struc_init cprog false false ctx conseq no_pos None *)
  (* in *)
  (* let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in *)
  (* flush stdout; *)
  (* let res = *)
  (*   if !Globals.disable_failure_explaining then ((not (CF.isFailCtx rs))) *)
  (*   else ((not (CF.isFailCtx_gen rs))) *)
  (* in *)
  let _ = Debug.ninfo_hprint (add_str "inf_vars" !CP.print_svl) inf_vars  no_pos in
  let () = x_tinfo_pp "lemproving: mytag1" no_pos in
  let (res, rs,_) = !sleek_entail 7 [] inf_vars  cprog [] ante conseq in
  let () = x_tinfo_pp "lemproving: mytag2" no_pos in
  (res, rs)

(* the value of flag "exact" decides the type of entailment checking              *)
(*   None       -->  forbid residue in RHS when the option --classic is turned on *)
(*   Some true  -->  always check entailment exactly (no residue in RHS)          *)
(*   Some false -->  always check entailment inexactly (allow residue in RHS)     *)
let run_entail_check inf_obj ctx (iante : lem_formula) (iconseq : lem_formula) (inf_vars: CP.spec_var list) (cprog: C.prog_decl) (exact_flag : bool option) =
  let () = x_tinfo_pp "run_entail_check_x" no_pos in
  let allow_r = match exact_flag with
    | None -> if (!Globals.allow_lemma_residue) then Some false (* inexact *) else Some true (* exact *) 
    | _ -> exact_flag in
  (* TODO:WN Using wrap_inf_obj_obly cos inf_obj is not properly propated *)
  wrap_inf_obj_only inf_obj (wrap_classic x_loc allow_r (run_entail_check_helper ctx iante iconseq inf_vars)) cprog

let run_entail_check inf_obj ctx (iante : lem_formula) (iconseq : lem_formula) 
    (inf_vars: CP.spec_var list) (cprog: C.prog_decl) (exact : bool option) =
  let pr_ctx = add_str "ctx: " Cprinter.string_of_list_context in
  let pr_ante = add_str "ante: " string_of_lem_formula in
  let pr_conseq = add_str "conseq: " string_of_lem_formula in
  let pr_vars = add_str "inf_vars: " (pr_list Cprinter.string_of_spec_var) in
  let pr_exact = add_str "exact: " (pr_opt string_of_bool) in
  let () = x_tinfo_pp "run_entail_check" no_pos in
  let pr_out (res, ctx_lst) = (
    ((add_str "\nresult: " string_of_bool) res) ^ "\n" ^
    ((add_str "list context: " Cprinter.string_of_list_context) ctx_lst) 
  ) in
  Debug.no_5 "run_entail_check"
    pr_ctx pr_ante pr_conseq pr_vars pr_exact pr_out
    (fun _ _ _ _ _ -> run_entail_check inf_obj ctx iante iconseq inf_vars cprog exact) 
    ctx iante iconseq inf_vars exact

let print_exc (check_id: string) =
  print_backtrace_quiet ();
  dummy_exception() ; 
  print_string_quiet ("exception in " ^ check_id ^ " check\n")

(* calls the entailment method and catches possible exceptions *)
let process_coercion_check coerc iante iconseq (inf_vars: CP.spec_var list) iexact (lemma_name: string) (cprog: C.prog_decl)  =
  let () = if  (!Globals.dump_lem_proc)||true then  
      let () = x_tinfo_pp "process_coercion_check" no_pos in
      let () = x_tinfo_pp "======================" no_pos in
      let () = x_tinfo_hp (add_str "i-ante" string_of_lem_formula) iante no_pos in
      let () = x_tinfo_hp (add_str "i-conseq" string_of_lem_formula) iconseq no_pos in ()
    else () in
  let inf_obj = coerc.Cast.coercion_infer_obj in
  let () = y_tinfo_hp (add_str "coerc:infer_obj" (fun e -> e # string_of)) inf_obj in
  let empty_es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let empty_es = { empty_es with CF.es_infer_obj = inf_obj } in
  let empty_ctx = CF.Ctx empty_es in
  let dummy_ctx = CF.SuccCtx [empty_ctx] in

  (* CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos]  *)
  try 
    (* TODO:WN local inf_obj not properly propagated *)
    let (b,lc) as res = run_entail_check inf_obj dummy_ctx iante iconseq inf_vars cprog (if iexact then Some true else None) in
    (* let () = Debug.info_hprint (add_str "inf_vars" !CP.print_svl) inf_vars no_pos in *)
    (* (if inf_vars!=[] then *)
    (*   let () = Debug.info_pprint "writing to residue " no_pos in *)
    (*   CF.residues := Some (lc,b)); *)
    res
  with e ->
    let exc_str = Printexc.to_string e in
    let err_msg = "exception " ^ exc_str ^ " in lemma proving" in
    print_exc ("lemma \""^ lemma_name ^"\""); 
    let rs = (CF.FailCtx (CF.Trivial_Reason (CF.mk_failure_must err_msg lemma_error, []),
                          empty_ctx,
                          (* (CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos), *) 
                          CF.mk_cex true )) in
    (false, rs)

let process_coercion_check coerc iante0 iconseq0 (inf_vars: CP.spec_var list) iexact (lemma_name: string) (cprog: C.prog_decl) =
  let pr = string_of_lem_formula in
  let pr3 = Cprinter.string_of_spec_var_list in
  let pr_out = pr_pair string_of_bool (Cprinter.string_of_list_context) in
  Debug.no_4 "process_coercion_check" pr pr (add_str "inf_vars" pr3) (add_str "iexact" string_of_bool) pr_out 
    (fun _ _ _ _ -> process_coercion_check coerc iante0 iconseq0 inf_vars iexact lemma_name cprog) iante0 iconseq0 inf_vars iexact

(* prepares the lhs&rhs of the coercion to be checked 
   - unfold lhs once
   - sets lhs and rhs original-derived flag to original in order to be able to inductively apply the current lemma in its proving
   - resets lhs & rhs view origins (originis = [])
   - renames self to self_<lemma_name>
*)(*
let check_coercion coer lhs rhs  (cprog: C.prog_decl) =
  let pos = CF.pos_of_formula coer.C.coercion_head in
  let lhs = Solver.unfold_nth 9 (cprog,None) lhs (CP.SpecVar (Globals.null_type, self, Unprimed)) true 0 pos in
  (* unfolding RHS need to use unflattened body to preserve case-spec *)
  let rhs = x_add Solver.unfold_struc_nth 9 (cprog,None) rhs (CP.SpecVar (Globals.null_type, self, Unprimed)) true 0 pos in
  (*let () = print_string("lhs_unfoldfed: "^(Cprinter.string_of_formula lhs)^"\n") in*)
  let lhs = if(coer.C.coercion_case == C.Ramify) then 
    Mem.ramify_unfolded_formula lhs cprog.C.prog_view_decls 
  else lhs
  in
  (*let () = print_string("lhs_unfoldfed_ramified: "^(Cprinter.string_of_formula lhs)^"\n") in*)
  let lhs = CF.add_original lhs true in
  let lhs = CF.reset_origins lhs in
  let rhs = CF.add_original rhs true in
  let rhs = CF.reset_origins rhs in
  let self_sv_lst = (CP.SpecVar (Globals.null_type, self, Unprimed)) :: [] in
  let self_sv_renamed_lst = (CP.SpecVar (Globals.null_type, (self ^ "_" ^ coer.C.coercion_name), Unprimed)) :: [] in
  let lhs = CF.subst_avoid_capture self_sv_lst self_sv_renamed_lst lhs in
  let rhs = CF.subst_avoid_capture self_sv_lst self_sv_renamed_lst rhs in
  x_add process_coercion_check coer (CFormula lhs) (CFormula rhs) coer.C.coercion_exact coer.C.coercion_name cprog 

let check_coercion coer lhs rhs  (cprog: C.prog_decl) =
  let pr1 = Cprinter.string_of_coercion in
  let pr2 = Cprinter.string_of_formula in
  Debug.no_3 "check_coercion" pr1 pr2 pr2 (fun (valid,rs) -> string_of_bool valid) (fun _ _ _ -> check_coercion coer lhs rhs cprog ) coer lhs rhs*)


let add_exist_heap_of_struc (fv_lhs:CP.spec_var list) (e : CF.struc_formula) : CF.struc_formula * (CP.spec_var list) =
  let e_implicit_vars = (* CF.struc_implicit_vars e *) [] in
  let f_none _ _ = None in
  let c_h_formula qvs fv_lhs x =  
    let vs = CF.h_fv x in
    let hrels = List.map (fun (a,_) -> a) (CF.get_HRels x ) in
    (* let hrels = Gen.BList.difference_eq CP.eq_spec_var hrels qvs in *)
    let vs = Gen.BList.difference_eq CP.eq_spec_var vs (fv_lhs@qvs@hrels@e_implicit_vars) in
    (x, vs) in
  let f_f fv_lhs e = 
    match e with
    | CF.Base ({CF.formula_base_heap = hf}) -> 
      let (n_hf,vs) = c_h_formula [] fv_lhs hf in
      Some (CF.push_exists vs e,vs)
    | CF.Exists ({CF.formula_exists_heap = hf; 
                  CF.formula_exists_qvars = qvs}) 
      -> 
      (* let fv_lhs = Gen.BList.difference_eq CP.eq_spec_var fv_lhs qvs in *)
      let (n_hf,vs) = c_h_formula qvs fv_lhs hf in
      Some (CF.push_exists vs e,vs)
    | _ -> None 
  in
  let f1 a e = Some(e,[]) in
  let f2 a e = None in
  let f_pure = (f1,f2,f2) in
  let f_memo a e = Some(e,[]) in
  let f_arg =
    let f1 e _ = e in
    (f1,f1,f1,(f1,f1,f1),f1) in
  let f_gen = (f_none, f_f, f_none, f_pure, f_memo) in
  let (a,b) = CF.trans_n_struc_formula e fv_lhs f_gen f_arg (fun a -> List.concat a) in
  (a,b)

let add_exist_heap_of_struc (fv_lhs:CP.spec_var list) (e : CF.struc_formula) : CF.struc_formula * (CP.spec_var list) 
  = 
  let pr1 = Cprinter.string_of_spec_var_list in
  let pr2 = Cprinter.string_of_struc_formula in
  Debug.no_2 "add_exist_heap_of_struc" pr1 pr2 (pr_pair pr2 pr1) add_exist_heap_of_struc fv_lhs e

(* same effect as check_coercion with the difference that the rhs is a struc_formula *)
let check_coercion_struc coer lhs rhs (cprog: C.prog_decl) =
  let pr_debug = Debug.ninfo_hprint in
  let is_singl sv0 svl=
    match svl with
    |[sv] -> CP.eq_spec_var sv0 sv
    | _ -> false
  in
  let is_iden_unfold lhs_unfold_ptr rhs_unfold_ptr lhs_vns rhs_vns =
    try
      let lhs_vn = List.find (fun vn -> CP.eq_spec_var vn.CF.h_formula_view_node lhs_unfold_ptr) lhs_vns in
      let rhs_vn = List.find (fun vn -> CP.eq_spec_var vn.CF.h_formula_view_node rhs_unfold_ptr) rhs_vns in
      (CP.eq_spec_var lhs_vn.CF.h_formula_view_node rhs_vn.CF.h_formula_view_node) &&
      (String.compare lhs_vn.CF.h_formula_view_name rhs_vn.CF.h_formula_view_name = 0)
    with _ -> true
  in
  let pos = CF.pos_of_formula coer.C.coercion_head in
  let fv_lhs = CF.fv lhs in
  (* let is_folding_flag = Cast.is_folding_coercion coer (\* && !Globals.adhoc_flag_3 *\) in *)
  (* let () = y_tinfo_hp (add_str "is_folding_coerc" string_of_bool) is_folding_flag in *)
  let () = y_tinfo_hp (add_str "coerc" Cprinter.string_of_coerc) coer in
  let () = y_tinfo_hp (add_str "LP.lhs" Cprinter.string_of_formula) lhs in
  let () = y_tinfo_hp (add_str "LP.fv_lhs" Cprinter.string_of_spec_var_list) fv_lhs in
  let fv_rhs = CF.struc_fv rhs in
  let () = y_tinfo_hp (add_str "rhs" Cprinter.string_of_struc_formula) rhs in
  (* WN : fv_rhs2 seems incorrect as it does not pick free vars of rhs *)
  let (new_rhs,fv_rhs2) = add_exist_heap_of_struc fv_lhs rhs in
  (* let () = y_tinfo_hp (add_str "new_rhs" Cprinter.string_of_struc_formula) new_rhs in *)
  let sv_self = (CP.SpecVar (Globals.null_type, self, Unprimed)) in
  let lhs_sv_self = try
    List.find (fun (CP.SpecVar (_,id,_)) -> id=self) fv_lhs
  with _ -> sv_self
  in
  let rhs_sv_self = try
    List.find (fun (CP.SpecVar (_,id,_)) -> id=self) fv_rhs
  with _ -> sv_self
  in
  let () = y_tinfo_hp (add_str "lhs_sv_self" !CP.print_sv) lhs_sv_self in
  let () = y_tinfo_hp (add_str "rhs_sv_self" !CP.print_sv) rhs_sv_self in
  (* let () = print_endline ("\n== old lhs = " ^ (Cprinter.string_of_formula lhs)) in *)
  let lhs_unfold_ptrs0,rhs_unfold_ptrs0 =
    (* let lhs_pt = if !Globals.enable_lemma_lhs_unfold then  *)
    (*     if !Globals.allow_lemma_deep_unfold then *)
    (*       CF.look_up_reachable_ptrs_f cprog lhs [sv_self] true true *)
    (*     else [sv_self] else [] in *)
    (* let rhs_pt = if !Globals.enable_lemma_rhs_unfold then  *)
    (*     if !Globals.allow_lemma_deep_unfold then *)
    (*       CF.look_up_reachable_ptrs_f cprog rhs [sv_self] true true *)
    (*     else [sv_self] else [] in *)
    if !Globals.enable_lemma_lhs_unfold || !Globals.enable_lemma_rhs_unfold then ([],[]) 
    else (* must re-check this -if- {**} *)
      (* rhs_unfold_ptrs below really needed? isn't lhs unfold enough? *)
      let lhs_unfold_ptrs = x_add CFU.look_up_reachable_ptrs_f cprog lhs [lhs_sv_self] true true in
      let rhs_unfold_ptrs = x_add CFU.look_up_reachable_ptrs_sf cprog new_rhs [rhs_sv_self] true true in
      let () = y_tinfo_hp (add_str "lhs_unfold_ptrs" !CP.print_svl) lhs_unfold_ptrs in
      let () = y_tinfo_hp (add_str "rhs_unfold_ptrs" !CP.print_svl) rhs_unfold_ptrs in
      if is_singl lhs_sv_self lhs_unfold_ptrs then
        if is_singl rhs_sv_self rhs_unfold_ptrs then
          let lhs_vns = CF.get_views lhs in
          let rhs_vns = CF.get_views_struc new_rhs in
          let () = y_tinfo_hp (add_str "lhs" !CF.print_formula) lhs in
          let () = y_tinfo_hp (add_str "new_rhs" !CF.print_struc_formula) new_rhs in
          let () = y_tinfo_hp (add_str "lhs_vns" (pr_list (fun v -> !CF.print_h_formula (CF.ViewNode v)))) lhs_vns in
          let () = y_tinfo_hp (add_str "rhs_vns" (pr_list (fun v -> !CF.print_h_formula (CF.ViewNode v)))) rhs_vns in
          if is_iden_unfold sv_self sv_self lhs_vns rhs_vns then
            let () = x_tinfo_hp (add_str "xxx" pr_id) "1" pos in
            [lhs_sv_self],[]
          else
            (* if List.length (CF.get_dnodes lhs) = 0 &&  List.length (CF.get_dnodes_struc new_rhs) =0 then [],[] else *)
            [lhs_sv_self],[rhs_sv_self]
        else
          [lhs_sv_self],[]
      else begin
        if is_singl rhs_sv_self rhs_unfold_ptrs then
          let () = x_tinfo_hp (add_str "xxx" pr_id) "2" pos in
          (CP.diff_svl lhs_unfold_ptrs rhs_unfold_ptrs),[rhs_sv_self]
        else if !Globals.allow_lemma_deep_unfold then
          let l_ptrs = if lhs_unfold_ptrs != [] then [lhs_sv_self] else [] in
          let r_ptrs = if rhs_unfold_ptrs != [] then [rhs_sv_self] else [] in
          (l_ptrs, r_ptrs)
        else
          (CP.diff_svl lhs_unfold_ptrs rhs_unfold_ptrs, CP.diff_svl rhs_unfold_ptrs lhs_unfold_ptrs)
      end
  in
  let () = y_tinfo_hp (add_str "lhs_unfold_ptrs0" !CP.print_svl) lhs_unfold_ptrs0 in
  let () = y_tinfo_hp (add_str "rhs_unfold_ptrs0" !CP.print_svl) rhs_unfold_ptrs0 in
  let lhs_unfold_ptrs = if !Globals.enable_lemma_lhs_unfold then
      if !Globals.allow_lemma_deep_unfold then
        CFU.look_up_reachable_ptrs_f cprog lhs [lhs_sv_self] true true
      else [lhs_sv_self]
    else
      lhs_unfold_ptrs0
  in
  let () = y_tinfo_hp (add_str "LP.lhs" Cprinter.string_of_formula) lhs in
  let lhs_hp_vars = List.filter CP.is_hp_typ (CF.fv lhs) in
  let (lhs,_) = (
    List.fold_left (fun (f,ss) sv0 ->
        (* should not use subst_var_par since type of spec_var may have been different i.e. null type *)
        (* let sv = CP.subst_var_par ss sv0 in *)
        let sv = CP.subs_one ss sv0 in
        (* let () = print_endline ("-- unfold lsh on " ^ (Cprinter.string_of_spec_var sv)) in *)
        let nf, ss1 = Solver.unfold_nth 9 (cprog, None) f sv ~lem_unfold:!Globals.enable_lemma_unk_unfold true 0 pos in
        let () = y_tinfo_hp (add_str "unfold:f" !CF.print_formula) f in
        let () = y_tinfo_hp (add_str "unfold:sv" !CF.print_sv) sv in
        let () = y_tinfo_hp (add_str "unfold:nf" !CF.print_formula) nf in
        (nf, ss@ss1)
      ) (lhs, []) lhs_unfold_ptrs
  ) in
  let unfolded_lhs_hp_vars = List.filter CP.is_hp_typ (CF.fv lhs) in
  let new_hp_infer_vars = Gen.BList.difference_eq CP.eq_spec_var unfolded_lhs_hp_vars lhs_hp_vars in
  (* let () = print_endline ("== new lhs = " ^ (Cprinter.string_of_formula lhs)) in *)
  let () = y_tinfo_hp (add_str "LP.lhs(unfolded)" Cprinter.string_of_formula) lhs in
  (*let () = print_string("lhs_unfoldfed_struc: "^(Cprinter.string_of_formula lhs)^"\n") in*)
  let glob_vs_rhs = Gen.BList.difference_eq CP.eq_spec_var fv_rhs fv_lhs in
  let () = pr_debug (add_str "LP.rhs" Cprinter.string_of_struc_formula) rhs pos in
  let () = y_tinfo_hp (add_str "LP.new_rhs" Cprinter.string_of_struc_formula) new_rhs in
  let () = pr_debug (add_str "LP.glob_vs_rhs" Cprinter.string_of_spec_var_list) glob_vs_rhs pos in
  let () = pr_debug (add_str "LP.fv_rhs" Cprinter.string_of_spec_var_list) fv_rhs pos in
  
  (* let vs_rhs = CF.fv_s rhs in *)
  (* let () = print_endline ("== old rhs = " ^ (Cprinter.string_of_struc_formula rhs)) in *)
  let rhs =
    (* make sure RHS is unfolded if LHS is not unfolded *)
    let rhs_unfold_ptrs = if lhs_unfold_ptrs==[] || 
                             !Globals.enable_lemma_rhs_unfold (* || is_folding_flag *) then
        if !Globals.allow_lemma_deep_unfold then
          CFU.look_up_reachable_ptrs_sf cprog new_rhs [sv_self] true true
        else [sv_self]
      else  []                          (* rhs_unfold_ptrs0  *) (*cancelling the effect of computing the pointers in the -if- {**} above *)
    in
    let unfolded_rhs = List.fold_left (fun sf sv ->
        Solver.unfold_struc_nth 9 (cprog,None) sf sv true 0 pos
      ) new_rhs rhs_unfold_ptrs in
    let () = y_tinfo_hp (add_str "LP.unfolded_rhs" Cprinter.string_of_struc_formula) unfolded_rhs in
    (* WN : elim_exists on RHS caused unsoundness for lemma proving! *)
    (* WN : rhs of entailment need to be in normalized state! *)
    (* CF.struc_elim_exist *) unfolded_rhs
  in
  (* let () = print_endline ("== new rhs = " ^ (Cprinter.string_of_struc_formula rhs)) in *)
  let () = y_tinfo_hp (add_str "LP.rhs(after elim_exists)" Cprinter.string_of_struc_formula) rhs in
  let lhs = if(coer.C.coercion_case == C.Ramify) then 
      Mem.ramify_unfolded_formula lhs cprog.C.prog_view_decls 
    else lhs
  in
  (* let () = print_string("lhs_unfoldfed_ramified: "^(Cprinter.string_of_formula lhs)^"\n") in *)
  let lhs = CF.add_original lhs true in
  let lhs = CF.reset_origins lhs in
  let rhs = CF.add_struc_original true rhs in
  let rhs = CF.reset_struc_origins rhs in
  let self_sv_lst = [lhs_sv_self] in
  let self_sv_renamed_lst = [CP.SpecVar ((* Globals.null_type *)CP.type_of_spec_var lhs_sv_self, (self ^ "_" ^ coer.C.coercion_name), Unprimed)] in
  let lhs = CF.subst_avoid_capture self_sv_lst self_sv_renamed_lst lhs in
  let rhs = CF.subst_struc_avoid_capture self_sv_lst self_sv_renamed_lst rhs in
  (* let rhs = CF.case_to_disjunct rhs in *)
  let () = y_tinfo_hp (add_str "coercion_exact" string_of_bool) coer.C.coercion_exact in
  let () = y_tinfo_hp (add_str "is_classic" string_of_bool) (coer.C.coercion_infer_obj # is_classic) in
  x_add process_coercion_check coer (CFormula lhs) (CSFormula rhs) (coer.C.coercion_infer_vars @ new_hp_infer_vars)
    coer.C.coercion_exact (* (coer.C.coercion_infer_obj # is_classic) *) coer.C.coercion_name cprog

let check_coercion_struc coer lhs rhs (cprog: C.prog_decl) =
  if Cast.folding_coercion coer then 
    Solver.wrapper_lemma_soundness x_loc coer 
      (check_coercion_struc coer lhs rhs) cprog
  else check_coercion_struc coer lhs rhs cprog

let check_coercion_struc coer lhs rhs (cprog: C.prog_decl) =
  let pr1 = Cprinter.string_of_coercion in
  let pr2 = Cprinter.string_of_formula in
  let pr3 = Cprinter.string_of_struc_formula in
  Debug.no_3 "check_coercion_struc" pr1 pr2 pr3 (fun (valid,rs) -> string_of_bool valid) 
    (fun _ _ _ -> check_coercion_struc coer lhs rhs cprog ) coer lhs rhs

(* sets the lhs & rhs of the entailment when proving l2r lemma (coercion), where the rhs (coercion body) is normalized  *)
let check_left_coercion coer (cprog: C.prog_decl) =
  (* using normalization form of lemma body and head to check *)
  let pr_debug = x_tinfo_hp in
  let pr = Cprinter.string_of_coerc_med in
  let pr2 = Cprinter.string_of_struc_formula in
  let pr3 = Cprinter.string_of_formula in
  let ent_lhs =coer.C.coercion_head_norm in
  let ent_rhs =  coer.C.coercion_body_norm in
  (* let ent_lhs = coer.C.coercion_head in                                    *)
  (* let ent_rhs = CF.struc_formula_of_formula coer.C.coercion_body no_pos in *)
  x_tinfo_pp "Verify Left Coercion" no_pos;
  pr_debug (add_str "lemma(med)" pr) coer no_pos;
  pr_debug (add_str "norm lhs" pr3) ent_lhs no_pos;
  pr_debug (add_str "norm rhs" pr2) ent_rhs no_pos;
  let (r,ctx) = x_add check_coercion_struc coer ent_lhs ent_rhs cprog in
  pr_debug (add_str "Verify Lemma success? :" string_of_bool) r no_pos;
  (r,ctx)


let check_left_coercion coer cprog  =
  let pr = Cprinter.string_of_coercion in
  let pr_out = pr_pair string_of_bool !CF.print_list_context in
  Debug.no_1 "check_left_coercion" pr pr_out 
    (fun _ -> check_left_coercion coer cprog ) coer

(* sets the lhs & rhs of the entailment when proving r2l lemma (coercion), where the rhs (coercion head) is normalized  *)
let check_right_coercion coer (cprog: C.prog_decl) =
  (* using normalization form of lemma body and head to check *)
  let pr_debug = x_tinfo_hp in
  let pr = Cprinter.string_of_coerc_med in
  let pr2 = Cprinter.string_of_struc_formula in
  let pr3 = Cprinter.string_of_formula in
  let ent_rhs = CF.struc_formula_of_formula coer.C.coercion_head_norm no_pos in
  let ent_lhs = CF.struc_to_formula coer.C.coercion_body_norm in
  (* let ent_lhs = Cvutil.remove_imm_from_formula cprog ent_lhs (CP.ConstAnn(Lend)) in *) (* actually this removes @L nodes from the body of right lemma for proving sake *)
  x_tinfo_pp "Verify Right Coercion" no_pos;
  pr_debug (add_str "lemma(med)" pr) coer no_pos;
  pr_debug (add_str "norm lhs" pr3) ent_lhs no_pos;
  pr_debug (add_str "norm rhs" pr2) ent_rhs no_pos;
  let (r,ctx) = x_add check_coercion_struc coer ent_lhs ent_rhs cprog in
  pr_debug (add_str "Verify Lemma success? :" string_of_bool) r no_pos;
  (r,ctx)

let check_right_coercion coer (cprog: C.prog_decl) =
  let pr = Cprinter.string_of_coercion in
  Debug.no_1 "check_right_coercion" pr (fun (valid,_) -> string_of_bool valid) (fun _ -> check_right_coercion coer cprog ) coer

(* interprets the entailment results for proving lemma validity and prints failure cause is case lemma is invalid *)
let print_lemma_entail_result ?(force_pr=false) (valid: bool) (ctx: CF.list_context) (num_id: string) =
  let force_print = force_pr || !Globals.lemma_ep_verbose ||  !Globals.lemma_ep in
  match valid with
  | true -> if force_print then print_string_quiet (num_id ^ ": Valid.\n") else ()
  | false ->
    let s = 
      if !Globals.disable_failure_explaining then ""
      else if !Globals.enable_error_as_exc then
        let final_error_opt = CF.get_final_error ctx in
        match final_error_opt with
        | Some (s, _, fk) -> begin
            match fk with
            | CF.Failure_May _ -> "(may) cause:"^s
            | CF.Failure_Must _ -> "(must) cause:"^s
            | _ -> "INCONSISTENCY : expected failure but success instead"
          end
        | None -> "INCONSISTENCY : expected failure but success instead"
      else
        match CF.get_must_failure ctx with
        | Some (s,cex) -> let _, ns = Cformula.cmb_fail_msg ("(must) cause: " ^ s) cex in ns
        | _ -> (match CF.get_may_failure ctx with
            | Some (s,cex) -> let _, ns =  Cformula.cmb_fail_msg ("(may) cause: " ^ s) cex in ns
            | None -> "INCONSISTENCY : expected failure but success instead"
          )
    in if force_print then print_string_quiet (num_id ^ ": Fail. " ^ s ^ "\n")
    else ()

(* check the validity of the lemma where:
   l2r: "->" implication
   r2l: "<-" implication 
   cprog: cast program 
   coerc_name: lemma name
   coerc_type: lemma type (Right, Left or Equiv)
*)
let verify_lemma ?(force_pr=false) (l2r: C.coercion_decl list) (r2l: C.coercion_decl list) (cprog: C.prog_decl)  lemma_name lemma_type =
  let () = x_tinfo_pp "lemproving : verify_lemma called" no_pos in
  let coercs = l2r @ r2l in
  let coercs_info = List.map (fun c ->
      let typ_orig = (match c.C.coercion_type_orig with
                      | None -> c.C.coercion_type
                      | Some t -> t
                     ) in
      match c.C.coercion_type with
      | I.Left ->
        let (valid, rs) = check_left_coercion c cprog in
        (valid, rs, typ_orig)
      | I.Right ->
        let (valid, rs) = check_right_coercion c cprog in
        (valid, rs, typ_orig)
      | _ -> Error.report_error_msg "verify_lemma: expect Left or Right coercion type"
    ) coercs in
  let num_id = "\nEntailing lemma "^ lemma_name ^"" in
  let residues = (match lemma_type with
      | I.Equiv -> (
          let (valid1, rs1, typ1, valid2, rs2, typ2) = (match coercs_info with
              | c1::c2::[] ->
                let (valid1, rs1, typ1) = c1 in
                let (valid2, rs2, typ2) = c2 in
                (valid1, rs1, typ1, valid2, rs2, typ2)
              | _ -> Error.report_error_msg "verify_lemma: Eqiv-lemma expects 2 coercions"
            ) in
          let residue = CF.and_list_context rs1 rs2 in
          let valid = valid1 && valid2 in
          let () = (
              let () = x_tinfo_pp "lemproving: before print_lemma_entail_result" no_pos in
              if valid then print_lemma_entail_result ~force_pr:force_pr valid residue num_id
              else
                let force_print = (force_pr ||  !Globals.lemma_ep) || !Globals.lemma_ep_verbose in
                if force_print then Debug.info_pprint (num_id ^ ": Fail. Details below:\n") no_pos;
                let typ1_str = Cprinter.string_of_coercion_type typ1 in
                let typ2_str = Cprinter.string_of_coercion_type typ2 in
                let () = print_lemma_entail_result ~force_pr:force_pr valid1 rs1 ("\t \"" ^ typ1_str ^ "\" implication: ") in
                let () = print_lemma_entail_result ~force_pr:force_pr valid2 rs2 ("\t \"" ^ typ2_str ^ "\" implication: ") in
                let () = x_tinfo_pp "lemproving: after print_lemma_entail_result" no_pos in
                ()
                  
            ) in
          residue
      )
      | I.Left | I.Right -> (
        let () = x_tinfo_pp "lemproving: before print_lemma_entail_result" no_pos in
        let valid, rs, typ = (match coercs_info with
                              | c::[] -> c
                              | _ -> Error.report_error_msg "verify_lemma: Left- or Right-lemma expects 1 coercion" 
                             ) in
        let () = print_lemma_entail_result ~force_pr:force_pr valid rs num_id  in rs
      )
    ) in
  residues
(* else None *)

let verify_lemma ?(force_pr=false) (l2r: C.coercion_decl list) (r2l: C.coercion_decl list) (cprog: C.prog_decl)
    coerc_name coerc_type  =
  wrap_proving_kind PK_Verify_Lemma ((verify_lemma ~force_pr:force_pr l2r r2l cprog coerc_name)) coerc_type

let verify_lemma ?(force_pr=false) caller (l2r: C.coercion_decl list) (r2l: C.coercion_decl list) (cprog: C.prog_decl)  coerc_name coerc_type =
  let pr_t = Iprinter.string_of_coerc_type in
  let pr = pr_list Cprinter.string_of_coercion in
  Debug.no_4_num caller "verify_lemma" pr pr (fun x -> x) pr_t (Cprinter.string_of_list_context) 
    (fun _ _ _ _ -> verify_lemma ~force_pr:force_pr l2r r2l cprog coerc_name coerc_type) l2r r2l coerc_name coerc_type


(* check the validity of the lemma where:
   l2r: "->" implication
   r2l: "<-" implication 
   cprog: cast program (needed for unfolding)
*)
let sa_verify_lemma cprog (lem:C.coercion_decl) =
  match lem.C.coercion_type with
  | I.Left -> check_left_coercion lem cprog
  | I.Right -> check_right_coercion lem cprog
  | I.Equiv -> failwith "Equiv not handled in sa_verify_lemma"

let sa_verify_lemma cprog (lem: C.coercion_decl) =
  let pr = Cprinter.string_of_coercion in
  Debug.no_1 "sa_verify_lemma" pr pr_none 
    (fun _ -> sa_verify_lemma cprog lem) lem


