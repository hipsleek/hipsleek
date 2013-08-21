open Globals
open Wrapper
open Gen
open Others
open Label_only

module AS = Astsimp
module C  = Cast
module CF = Cformula
module CP = Cpure
module H  = Hashtbl
module I  = Iast

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
  let p,rl,hp = List.fold_left (fun (p,rl,hp) var -> 
      match var with
        | CP.SpecVar(RelT _,_,_) -> (p,var::rl,hp)
        | CP.SpecVar(HpT, _, _ ) -> (p,rl,var::hp)
        | _      -> (var::p,rl,hp)
  ) ([],[],[]) vrs in
  (p,rl,hp)

let add_infer_vars_to_ctx ivs ctx =
  let (p,rl,hp) = split_infer_vars ivs in
  let ctx = Infer.init_vars ctx p rl hp [] in 
  ctx
   

(* checks if iante(CF.formula) entails iconseq(CF.formula or CF.struc_formula) in cprog(C.prog_decl)
   - similar to Sleekengine.run_entail_check
*)
let run_entail_check_helper ctx (iante: lem_formula) (iconseq: lem_formula) (inf_vars: CP.spec_var list) (cprog: C.prog_decl)  =
  let ante = lem_to_cformula iante in
  (* let ante = Solver.prune_preds cprog true ante in (\* (andreeac) redundant? *\) *)
  let conseq = lem_to_struc_cformula iconseq in
  (* let conseq = Solver.prune_pred_struc cprog true conseq in (\* (andreeac) redundant ? *\) *)
  (* let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in *)
  (* let ctx = CF.build_context ctx ante no_pos in *)
  let ctx = match ctx with
    | CF.SuccCtx l -> 
          let newl = List.map (fun ct -> 
              let nctx = CF.set_context_formula ct ante in
              let nctx = add_infer_vars_to_ctx inf_vars nctx in
              let nctx = CF.transform_context (Solver.elim_unsat_es 10 cprog (ref 1)) nctx in
              nctx
          ) l in CF.SuccCtx newl
    | CF.FailCtx _ ->    
          Error.report_error {Error.error_loc = no_pos; 
          Error.error_text = "Cannot Prove Lemma in a False Ctx "}
  in 
  (* let ctx = add_infer_vars_to_list_ctx inf_vars ctx in *)
  let _ = if !Globals.print_core || !Globals.print_core_all then print_string ("\nrun_entail_check_helper:\n"^(Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") else () in
  (* let ctx = CF.transform_list_context (Solver.elim_unsat_es 10 cprog (ref 1)) ctx in *)
  let rs1, _ = 
  if not !Globals.disable_failure_explaining then
    Solver.heap_entail_struc_init_bug_inv cprog false false ctx conseq no_pos None
  else
     Solver.heap_entail_struc_init cprog false false ctx conseq no_pos None
  in
  let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in
  flush stdout;
  let res =
    if !Globals.disable_failure_explaining then ((not (CF.isFailCtx rs)))
    else ((not (CF.isFailCtx_gen rs)))
  in
  (res, rs)

(* the value of flag "exact" decides the type of entailment checking              *)
(*   None       -->  forbid residue in RHS when the option --classic is turned on *)
(*   Some true  -->  always check entailment exactly (no residue in RHS)          *)
(*   Some false -->  always check entailment inexactly (allow residue in RHS)     *)
let run_entail_check ctx (iante : lem_formula) (iconseq : lem_formula) (inf_vars: CP.spec_var list) (cprog: C.prog_decl)    (exact : bool option) =
  wrap_classic (Some true) (* exact *) (run_entail_check_helper ctx iante iconseq inf_vars) cprog

let print_exc (check_id: string) =
  Printexc.print_backtrace stdout;
  dummy_exception() ; 
  print_string ("exception in " ^ check_id ^ " check\n")

(* calls the entailment method and catches possible exceptions *)
let process_coercion_check iante iconseq (inf_vars: CP.spec_var list) iexact (lemma_name: string) (cprog: C.prog_decl)  =
  let dummy_ctx = CF.SuccCtx [CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos] in  
  try 
    let (b,lc) as res = run_entail_check dummy_ctx iante iconseq inf_vars cprog (if iexact then Some true else None) in
    (* let _ = Debug.info_hprint (add_str "inf_vars" !CP.print_svl) inf_vars no_pos in *)
    (* (if inf_vars!=[] then *)
    (*   let _ = Debug.info_pprint "writing to residue " no_pos in *)
    (*   CF.residues := Some (lc,b)); *)
    res
  with _ -> print_exc ("lemma \""^ lemma_name ^"\""); 
      let rs = (CF.FailCtx (CF.Trivial_Reason (CF.mk_failure_must "exception in lemma proving" lemma_error))) in
      (false, rs)

let process_coercion_check iante0 iconseq0 (inf_vars: CP.spec_var list) iexact (lemma_name: string) (cprog: C.prog_decl) =
  let pr = string_of_lem_formula in
  let pr3 = Cprinter.string_of_spec_var_list in
  let pr_out = pr_pair string_of_bool (Cprinter.string_of_list_context) in
  Debug.no_3 "process_coercion_check" pr pr pr3 pr_out 
      (fun _ _ _ -> process_coercion_check iante0 iconseq0 inf_vars iexact lemma_name cprog) iante0 iconseq0 inf_vars

(* prepares the lhs&rhs of the coercion to be checked 
   - unfold lhs once
   - sets lhs and rhs original-derived flag to original in order to be able to inductively apply the current lemma in its proving
   - resets lhs & rhs view origins (originis = [])
   - renames self to self_<lemma_name>
*)(*
let check_coercion coer lhs rhs  (cprog: C.prog_decl) =
  let pos = CF.pos_of_formula coer.C.coercion_head in
  let lhs = Solver.unfold_nth 9 (cprog,None) lhs (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
  (* unfolding RHS need to use unflattened body to preserve case-spec *)
  let rhs = Solver.unfold_struc_nth 9 (cprog,None) rhs (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
  (*let _ = print_string("lhs_unfoldfed: "^(Cprinter.string_of_formula lhs)^"\n") in*)
  let lhs = if(coer.C.coercion_case == C.Ramify) then 
    Mem.ramify_unfolded_formula lhs cprog.C.prog_view_decls 
  else lhs
  in
  (*let _ = print_string("lhs_unfoldfed_ramified: "^(Cprinter.string_of_formula lhs)^"\n") in*)
  let lhs = CF.add_original lhs true in
  let lhs = CF.reset_origins lhs in
  let rhs = CF.add_original rhs true in
  let rhs = CF.reset_origins rhs in
  let self_sv_lst = (CP.SpecVar (Named "", self, Unprimed)) :: [] in
  let self_sv_renamed_lst = (CP.SpecVar (Named "", (self ^ "_" ^ coer.C.coercion_name), Unprimed)) :: [] in
  let lhs = CF.subst_avoid_capture self_sv_lst self_sv_renamed_lst lhs in
  let rhs = CF.subst_avoid_capture self_sv_lst self_sv_renamed_lst rhs in
  process_coercion_check (CFormula lhs) (CFormula rhs) coer.C.coercion_exact coer.C.coercion_name cprog 

let check_coercion coer lhs rhs  (cprog: C.prog_decl) =
  let pr1 = Cprinter.string_of_coercion in
  let pr2 = Cprinter.string_of_formula in
  Debug.no_3 "check_coercion" pr1 pr2 pr2 (fun (valid,rs) -> string_of_bool valid) (fun _ _ _ -> check_coercion coer lhs rhs cprog ) coer lhs rhs*)


let add_exist_heap_of_struc (fv_lhs:CP.spec_var list) (e : CF.struc_formula) : CF.struc_formula * (CP.spec_var list) =
  let f_none _ _ = None in
  let c_h_formula qvs fv_lhs x =  
    let vs = CF.h_fv x in
    let hrels = List.map (fun (a,_) -> a) (CF.get_HRels x ) in
    (* let hrels = Gen.BList.difference_eq CP.eq_spec_var hrels qvs in *)
    let vs = Gen.BList.difference_eq CP.eq_spec_var vs (fv_lhs@qvs@hrels) in
    (x, vs) in
  let f_f fv_lhs e = 
    match e with
      | CF.Base ({CF.formula_base_heap = hf}) 
          -> let (n_hf,vs) = c_h_formula [] fv_lhs hf in
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
  let pos = CF.pos_of_formula coer.C.coercion_head in
  let fv_lhs = CF.fv lhs in
  let _ = Debug.tinfo_hprint (add_str "LP.lhs" Cprinter.string_of_formula) lhs pos in
  let _ = Debug.tinfo_hprint (add_str "LP.fv_lhs" Cprinter.string_of_spec_var_list) fv_lhs pos in
  let lhs = Solver.unfold_nth 9 (cprog,None) lhs (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
  let _ = Debug.tinfo_hprint (add_str "LP.lhs(unfolded)" Cprinter.string_of_formula) lhs pos in
  (*let _ = print_string("lhs_unfoldfed_struc: "^(Cprinter.string_of_formula lhs)^"\n") in*)
  let (new_rhs,fv_rhs) = add_exist_heap_of_struc fv_lhs rhs in
  let glob_vs_rhs = Gen.BList.difference_eq CP.eq_spec_var fv_rhs fv_lhs in
  let _ = Debug.tinfo_hprint (add_str "LP.rhs" Cprinter.string_of_struc_formula) rhs pos in
  let _ = Debug.tinfo_hprint (add_str "LP.new_rhs" Cprinter.string_of_struc_formula) new_rhs pos in
  let _ = Debug.tinfo_hprint (add_str "LP.glob_vs_rhs" Cprinter.string_of_spec_var_list) glob_vs_rhs pos in
  let _ = Debug.tinfo_hprint (add_str "LP.fv_rhs" Cprinter.string_of_spec_var_list) fv_rhs pos in
  (* let vs_rhs = CF.fv_s rhs in *)
  let rhs = Solver.unfold_struc_nth 9 (cprog,None) new_rhs (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
  let _ = Debug.tinfo_hprint (add_str "LP.rhs(after unfold)" Cprinter.string_of_struc_formula) rhs pos in
  let lhs = if(coer.C.coercion_case == C.Ramify) then 
    Mem.ramify_unfolded_formula lhs cprog.C.prog_view_decls 
  else lhs
  in
  (*let _ = print_string("lhs_unfoldfed_ramified: "^(Cprinter.string_of_formula lhs)^"\n") in*)
  let lhs = CF.add_original lhs true in
  let lhs = CF.reset_origins lhs in
  let rhs = CF.add_struc_original true rhs in
  let rhs = CF.reset_struc_origins rhs in
  let self_sv_lst = (CP.SpecVar (Named "", self, Unprimed)) :: [] in
  let self_sv_renamed_lst = (CP.SpecVar (Named "", (self ^ "_" ^ coer.C.coercion_name), Unprimed)) :: [] in
  let lhs = CF.subst_avoid_capture self_sv_lst self_sv_renamed_lst lhs in
  let rhs = CF.subst_struc_avoid_capture self_sv_lst self_sv_renamed_lst rhs in
  (* let rhs = CF.case_to_disjunct rhs in *)
  process_coercion_check (CFormula lhs) (CSFormula rhs) coer.C.coercion_infer_vars coer.C.coercion_exact coer.C.coercion_name  cprog

let check_coercion_struc coer lhs rhs (cprog: C.prog_decl) =
  let pr1 = Cprinter.string_of_coercion in
  let pr2 = Cprinter.string_of_formula in
  let pr3 = Cprinter.string_of_struc_formula in
  Debug.no_3 "check_coercion_struc" pr1 pr2 pr3 (fun (valid,rs) -> string_of_bool valid) (fun _ _ _ -> check_coercion_struc coer lhs rhs cprog ) coer lhs rhs

(* sets the lhs & rhs of the entailment when proving l2r lemma (coercion), where the rhs (coercion body) is normalized  *)
let check_left_coercion coer (cprog: C.prog_decl) =
  (*let _ = print_string ("\nCoercion name: " ^ coer.C.coercion_name) in *)
  let ent_lhs =coer.C.coercion_head in
  let ent_rhs = CF.struc_formula_of_formula coer.C.coercion_body no_pos in
  (* let ent_rhs =  coer.C.coercion_body_norm in *)
  check_coercion_struc coer ent_lhs ent_rhs cprog

let check_left_coercion coer cprog  =
  let pr = Cprinter.string_of_coercion in
  Debug.no_1 "check_left_coercion" pr (fun (valid,_) -> string_of_bool valid) (fun _ -> check_left_coercion coer cprog ) coer

(* sets the lhs & rhs of the entailment when proving r2l lemma (coercion), where the rhs (coercion head) is normalized  *)
let check_right_coercion coer (cprog: C.prog_decl) =
  (* let _ = print_string ("\nCoercion name: " ^ coer.C.coercion_name) in *)
  let ent_rhs = CF.struc_formula_of_formula coer.C.coercion_head(* _norm *) no_pos in
  let ent_lhs = coer.C.coercion_body in
  check_coercion_struc coer ent_lhs ent_rhs cprog 

let check_right_coercion coer (cprog: C.prog_decl) =
  let pr = Cprinter.string_of_coercion in
  Debug.no_1 "check_right_coercion" pr (fun (valid,_) -> string_of_bool valid) (fun _ -> check_right_coercion coer cprog ) coer

(* interprets the entailment results for proving lemma validity and prints failure cause is case lemma is invalid *)
let print_lemma_entail_result (valid: bool) (ctx: CF.list_context) (num_id: string) =
  if valid then 
    let _ = print_string (num_id ^ ": Valid.\n") in ()
    (* print_string ((Cprinter.string_of_numbered_list_formula_trace_inst cprog *)
    (*     (CF.list_formula_trace_of_list_context ctx))^"\n" )  *)
  else let s = 
    if !Globals.disable_failure_explaining then ""
    else
      match CF.get_must_failure ctx with
        | Some s -> "(must) cause:" ^ s 
        | _ -> (match CF.get_may_failure ctx with
            | Some s -> "(may) cause:" ^ s
            | None -> "INCONSISTENCY : expected failure but success instead"
          )
  in print_string (num_id ^ ": Fail. " ^ s ^ "\n")

(* check the validity of the lemma where:
   l2r: "->" implication
   r2l: "<-" implication 
   cprog: cast program 
   coerc_name: lemma name
   coerc_type: lemma type (Right, Left or Equiv)
*)
let verify_lemma (l2r: C.coercion_decl option) (r2l: C.coercion_decl option) (cprog: C.prog_decl)  lemma_name lemma_type =
  (* if true (\* !Globals.check_coercions *\) then *)
  let helper coercs check_coerc = match coercs with
    | None -> (true, None)
    | Some coerc -> let (valid, rs) = check_coerc coerc cprog in (valid, Some rs)
  in
  let valid_l2r, rs_l2r = helper l2r (check_left_coercion) in
  let valid_r2l, rs_r2l = helper r2l (check_right_coercion) in
  let num_id = "\nEntailing lemma "^ lemma_name ^"" in
  let empty_resid = CF.FailCtx (CF.Trivial_Reason (CF.mk_failure_must "empty residue" Globals.lemma_error)) in
  let (rs1, rs2) = match (rs_l2r, rs_r2l) with
    | (None, None) -> (empty_resid, empty_resid)
    | (None, Some rsr) -> (empty_resid, rsr)
    | (Some rsl, None) -> (rsl, empty_resid)
    | (Some rsl_, Some rsr_) -> (rsl_, rsr_) in
  let residues = match lemma_type with
    | I.Equiv -> 
          let residue = CF.and_list_context rs1 rs2 in
          let valid = valid_l2r && valid_r2l in
          let _ = if valid then print_lemma_entail_result valid residue num_id 
          else 
            let _ = print_string (num_id ^ ": Fail. Details below:\n") in
            let _ = print_lemma_entail_result valid_l2r rs1 "\t \"->\" implication: " in
            let _ = print_lemma_entail_result valid_r2l rs2 "\t \"<-\" implication: " in
            ()
          in
          residue
    | I.Left -> let _ = print_lemma_entail_result valid_l2r rs1 num_id  in rs1
    | I.Right  -> let _ = print_lemma_entail_result valid_r2l rs2 num_id  in rs2
  in
  residues
  (* else None *)

let verify_lemma (l2r: C.coercion_decl option) (r2l: C.coercion_decl option) (cprog: C.prog_decl)
      coerc_name coerc_type  =
  wrap_proving_kind PK_Verify_Lemma
      ((* wrap_classic (Some true) *) (verify_lemma (l2r: C.coercion_decl option) (r2l: C.coercion_decl option) (cprog: C.prog_decl) coerc_name)) coerc_type

let verify_lemma caller (l2r: C.coercion_decl option) (r2l: C.coercion_decl option) (cprog: C.prog_decl)  coerc_name coerc_type =
  let pr c = match c with 
    | Some coerc -> Cprinter.string_of_coercion coerc
    | None -> ""
  in
  Debug.no_3_num caller "verify_lemma" pr pr (fun x -> x) (Cprinter.string_of_list_context) (fun _ _ _ -> verify_lemma l2r r2l cprog coerc_name coerc_type) l2r r2l coerc_name


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


