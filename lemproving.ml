open Globals
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

(* checks if iante(CF.formula) entails iconseq(CF.formula or CF.struc_formula) in cprog(C.prog_decl)
   - similar to Sleekengine.run_entail_check
*)
let run_entail_check_helper (iante: lem_formula) (iconseq: lem_formula) (cprog: C.prog_decl)  =
  let ante = lem_to_cformula iante in
  (* let ante = Solver.prune_preds cprog true ante in (\* (andreeac) redundant? *\) *)
  let conseq = lem_to_struc_cformula iconseq in
  (* let conseq = Solver.prune_pred_struc cprog true conseq in (\* (andreeac) redundant ? *\) *)
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let _ = if !Globals.print_core || !Globals.print_core_all then print_string ("\run_entail_check_helper:\n"^(Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") else () in
  let ctx = CF.transform_context (Solver.elim_unsat_es 10 cprog (ref 1)) ctx in
  let rs1, _ = 
  if not !Globals.disable_failure_explaining then
    Solver.heap_entail_struc_init_bug_inv cprog false false (CF.SuccCtx[ctx]) conseq no_pos None
  else
     Solver.heap_entail_struc_init cprog false false (CF.SuccCtx[ctx]) conseq no_pos None
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
let run_entail_check (iante : lem_formula) (iconseq : lem_formula) (cprog: C.prog_decl) (exact : bool option) =
  wrap_classic exact (run_entail_check_helper iante iconseq) cprog

let print_exc (check_id: string) =
  Printexc.print_backtrace stdout;
  dummy_exception() ; 
  print_string ("exception in " ^ check_id ^ " check\n")

(* calls the entailment method and catches possible exceptions *)
let process_coercion_check iante iconseq iexact (lemma_name: string)  (cprog: C.prog_decl)  =
  try 
    run_entail_check iante iconseq cprog (if iexact then Some true else None)
  with _ -> print_exc ("lemma \""^ lemma_name ^"\""); 
      let rs = (CF.FailCtx (CF.Trivial_Reason (CF.mk_failure_must "exception in lemma proving" lemma_error))) in
      (false, rs)

let process_coercion_check iante0 iconseq0 iexact(lemma_name: string)  (cprog: C.prog_decl) =
  let pr = string_of_lem_formula in
  Debug.no_2 "process_coercion_check" pr pr (fun _ -> "?") (fun _ _ -> process_coercion_check iante0 iconseq0 iexact lemma_name cprog) iante0 iconseq0

(* prepares the lhs&rhs of the coercion to be checked 
   - unfold lhs once
   - sets lhs and rhs original-derived flag to original in order to be able to inductively apply the current lemma in its proving
   - resets lhs & rhs view origins (originis = [])
   - renames self to self_<lemma_name>
*)
let check_coercion coer lhs rhs  (cprog: C.prog_decl) =
    let pos = CF.pos_of_formula coer.C.coercion_head in
    let lhs = Solver.unfold_nth 9 (cprog,None) lhs (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
	let rhs = Solver.unfold_nth 9 (cprog,None) rhs (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
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
  Debug.no_3 "check_coercion" pr1 pr2 pr2 (fun (valid,rs) -> string_of_bool valid) (fun _ _ _ -> check_coercion coer lhs rhs cprog ) coer lhs rhs

(* same effect as check_coercion with the difference that the rhs is a struc_formula *)
let check_coercion_struc coer lhs rhs (cprog: C.prog_decl) =
    let pos = CF.pos_of_formula coer.C.coercion_head in
    let lhs = Solver.unfold_nth 9 (cprog,None) lhs (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
    (*let _ = print_string("lhs_unfoldfed_struc: "^(Cprinter.string_of_formula lhs)^"\n") in*)
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
    process_coercion_check (CFormula lhs) (CSFormula rhs) coer.C.coercion_exact coer.C.coercion_name  cprog

let check_coercion_struc coer lhs rhs (cprog: C.prog_decl) =
  let pr1 = Cprinter.string_of_coercion in
  let pr2 = Cprinter.string_of_formula in
  let pr3 = Cprinter.string_of_struc_formula in
  Debug.no_3 "check_coercion_struc" pr1 pr2 pr3 (fun (valid,rs) -> string_of_bool valid) (fun _ _ _ -> check_coercion_struc coer lhs rhs cprog ) coer lhs rhs

(* sets the lhs & rhs of the entailment when proving l2r lemma (coercion), where the rhs (coercion body) is normalized  *)
let check_left_coercion coer (cprog: C.prog_decl) =
  (*let _ = print_string ("\nCoercion name: " ^ coer.C.coercion_name) in *)
  let ent_lhs =coer.C.coercion_head in
  let ent_rhs = coer.C.coercion_body_norm in
  check_coercion_struc coer ent_lhs ent_rhs cprog

let check_left_coercion coer cprog  =
  let pr = Cprinter.string_of_coercion in
  Debug.no_1 "check_left_coercion" pr (fun (valid,_) -> string_of_bool valid) (fun _ -> check_left_coercion coer cprog ) coer

(* sets the lhs & rhs of the entailment when proving r2l lemma (coercion), where the rhs (coercion head) is normalized  *)
let check_right_coercion coer (cprog: C.prog_decl) =
  (* let _ = print_string ("\nCoercion name: " ^ coer.C.coercion_name) in *)
  let ent_rhs = coer.C.coercion_head_norm in
  let ent_lhs = coer.C.coercion_body in
  check_coercion coer ent_lhs ent_rhs cprog 

let check_right_coercion coer (cprog: C.prog_decl) =
  let pr = Cprinter.string_of_coercion in
  Debug.no_1 "check_right_coercion" pr (fun (valid,_) -> string_of_bool valid) (fun _ -> check_right_coercion coer cprog ) coer

(* interprets the entailment results for proving lemma validity and prints failure cause is case lemma is invalid *)
let print_entail_result (valid: bool) (residue: CF.list_context) (num_id: string) =
  if valid then print_string (num_id ^ ": Valid.\n")
  else let s = 
    if !Globals.disable_failure_explaining then ""
    else
      match CF.get_must_failure residue with
        | Some s -> "(must) cause:" ^ s 
        | _ -> (match CF.get_may_failure residue with
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
  if !Globals.check_coercions then
    let helper coercs check_coerc = match coercs with
      | None -> (true, None)
      | Some coerc -> let (valid, rs) = check_coerc coerc cprog in (valid, Some rs)
    in
    let valid_l2r, rs_l2r = helper l2r check_left_coercion in
    let valid_r2l, rs_r2l = helper r2l check_right_coercion in
    let num_id = "\nEntailing lemma "^ lemma_name ^"" in
    let empty_resid = CF.FailCtx (CF.Trivial_Reason (CF.mk_failure_must "empty residue" Globals.lemma_error)) in
    let (rs1, rs2) = match (rs_l2r, rs_r2l) with
      | (None, None) -> (empty_resid, empty_resid)
      | (None, Some rsr) -> (empty_resid, rsr)
      | (Some rsl, None) -> (rsl, empty_resid)
      | (Some rsl_, Some rsr_) -> (rsl_, rsr_) in
    let residues = match lemma_type with
      | I.Equiv -> 
            let residue = CF.list_context_union rs1 rs2 in
            let valid = valid_l2r && valid_r2l in
            let _ = if valid then print_entail_result valid residue num_id
            else 
              let _ = print_string (num_id ^ ": Fail. Details below:\n") in
              let _ = print_entail_result valid_l2r rs1 "\t \"->\" implication: " in
              print_entail_result valid_r2l rs2 "\t \"<-\" implication: "
            in
            residue
      | I.Left -> let _ = print_entail_result valid_l2r rs1 num_id in rs1
      | I.Right  -> let _ = print_entail_result valid_r2l rs2 num_id in rs2
    in
    Some residues
  else None

let verify_lemma (l2r: C.coercion_decl option) (r2l: C.coercion_decl option) (cprog: C.prog_decl)  coerc_name coerc_type =
  let pr c = match c with 
    | Some coerc -> Cprinter.string_of_coercion coerc
    | None -> ""
  in
  Debug.no_3 "verify_lemma" pr pr (fun x -> x) (fun _ -> "Unit") (fun _ _ _ -> verify_lemma l2r r2l cprog coerc_name coerc_type) l2r r2l coerc_name
