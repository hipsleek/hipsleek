open Globals

module AS = Astsimp
module C  = Cast
module CF = Cformula
module CP = Cpure
module H  = Hashtbl
module I  = Iast


let run_entail_check iante0 iconseq0 cprog meta_to_formula =
  let (ante, conseq) = meta_to_formula iante0 iconseq0 cprog in
  (* let stab = H.create 103 in *)
  (* let ante =Sleekcommons.meta_to_formula iante0 false [] stab in     *)
  (* let ante = Solver.prune_preds !cprog true ante in *)
  (* let fvs = CF.fv ante in *)
  (* let fv_idents = List.map CP.name_of_spec_var fvs in *)
  (* let conseq = Sleekcommons.meta_to_struc_formula iconseq0 false fv_idents stab in *)
  (* let conseq = Solver.prune_pred_struc !cprog true conseq in *)
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) no_pos in
  let ctx = CF.build_context ectx ante no_pos in
  let _ = if !Globals.print_core then print_string ("\nrun_entail_check:\n"^(Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") else () in
  let ctx = CF.transform_context (Solver.elim_unsat_es cprog (ref 1)) ctx in
  let rs1, _ = 
  if not !Globals.disable_failure_explaining then
    Solver.heap_entail_struc_init_bug_inv cprog false false 
        (CF.SuccCtx[ctx]) conseq no_pos None
  else
     Solver.heap_entail_struc_init cprog false false 
        (CF.SuccCtx[ctx]) conseq no_pos None
  in
  let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in
  flush stdout;
  let res =
    if not !Globals.disable_failure_explaining then ((not (CF.isFailCtx_gen rs)))
    else ((not (CF.isFailCtx rs)))
  in
  (res, rs)

let print_entail_result (valid: bool) (residue: CF.list_context) (num_id: string) =
  if not valid then
    begin
      let s =
        if not !Globals.disable_failure_explaining then
          match CF.get_must_failure residue with
            | Some s -> "(must) cause:"^s 
            | _ -> (match CF.get_may_failure residue with
                | Some s -> "(may) cause:"^s
                | None -> "INCONSISTENCY : expected failure but success instead"
              )
        else ""
      in
      print_string (num_id^": Fail. "^s^"\n")
          (*if !Globals.print_err_sleek then *)
          (* ;print_string ("printing here: "^(Cprinter.string_of_list_context rs)) *)
    end
  else
    begin
	  print_string (num_id^": Valid.\n")
          (* ;print_string ("printing here: "^(Cprinter.string_of_list_context rs)) *)
    end  

let print_exc (check_id: string) =
  Printexc.print_backtrace stdout;
  dummy_exception() ; 
  print_string ("exception in " ^ check_id ^ " check\n")

let process_lemma_check iante0 iconseq0 (lemma_name: string) cprog meta_to_formula =
  try 
    run_entail_check iante0 iconseq0 cprog meta_to_formula
  with _ -> print_exc ("lemma \""^ lemma_name ^"\""); 
      let rs = (CF.FailCtx (CF.Trivial_Reason " exception in lemma proving ")) in
      (false, rs)

let process_lemma_check iante0 iconseq0 (lemma_name: string) cprog meta_to_formula =
  let pr = Cprinter.string_of_formula in
  Gen.Debug.no_2 "process_lemma_check" pr pr (fun _ -> "?") (fun _ _ -> process_lemma_check iante0 iconseq0 lemma_name cprog meta_to_formula) iante0 iconseq0

let check_coercion coer lhs rhs cprog meta_to_formula =
    let pos = CF.pos_of_formula coer.C.coercion_head in
    let lhs = Solver.unfold_nth 9 (cprog,None) lhs (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
    let lhs = CF.add_original lhs true in
    let lhs = CF.reset_origins lhs in
    let rhs = CF.add_original rhs true in
    let rhs = CF.reset_origins rhs in
    let self_sv_lst = (CP.SpecVar (Named "", self, Unprimed)) :: [] in
    let self_sv_renamed_lst = (CP.SpecVar (Named "", (self ^ "_" ^ coer.C.coercion_name), Unprimed)) :: [] in
    let lhs = CF.subst_avoid_capture self_sv_lst self_sv_renamed_lst lhs in
    let rhs = CF.subst_avoid_capture self_sv_lst self_sv_renamed_lst rhs in
    process_lemma_check lhs rhs coer.C.coercion_name cprog meta_to_formula

let check_coercion coer lhs rhs cprog meta_to_formula=
  let pr1 = Cprinter.string_of_coercion in
  let pr2 = Cprinter.string_of_formula in
  Gen.Debug.no_3 "check_coercion" pr1 pr2 pr2 (fun (valid,rs) -> string_of_bool valid) (fun _ _ _ -> check_coercion coer lhs rhs cprog meta_to_formula) coer lhs rhs

(* below expects struc_formula for rhs *)
let check_coercion_struc coer lhs rhs cprog meta_to_formula =
    let pos = CF.pos_of_formula coer.C.coercion_head in
    let lhs = Solver.unfold_nth 9 (cprog,None) lhs (CP.SpecVar (Named "", self, Unprimed)) true 0 pos in
    let lhs = CF.add_original lhs true in
    let lhs = CF.reset_origins lhs in
    let rhs = CF.add_struc_original rhs true in
    let rhs = CF.reset_struc_origins rhs in
    let self_sv_lst = (CP.SpecVar (Named "", self, Unprimed)) :: [] in
    let self_sv_renamed_lst = (CP.SpecVar (Named "", (self ^ "_" ^ coer.C.coercion_name), Unprimed)) :: [] in
    let lhs = CF.subst_avoid_capture self_sv_lst self_sv_renamed_lst lhs in
    let rhs = CF.subst_struc_avoid_capture self_sv_lst self_sv_renamed_lst rhs in
    process_lemma_check lhs rhs coer.C.coercion_name meta_to_formula

let check_left_coercion coer cprog  meta_to_formula =
  let ent_lhs =coer.C.coercion_head in
  let ent_rhs = coer.C.coercion_body_norm in
  check_coercion_struc coer ent_lhs ent_rhs cprog meta_to_formula

let check_right_coercion coer cprog  meta_to_formula =
  let ent_rhs = coer.C.coercion_head_norm in
  let ent_lhs = coer.C.coercion_body in
  check_coercion coer ent_lhs ent_rhs cprog meta_to_formula


let process_lemma (l2r: C.coercion_decl list) (r2l: C.coercion_decl list) (cprog: C.prog_decl)  coerc_name coerc_type meta_to_formula =
  if !Globals.check_coercions then begin
    let helper coercs check_coerc = match coercs with
      | [] -> (true, None)
      | coerc::[] -> let (valid, rs) = check_coerc coerc cprog meta_to_formula in (valid, Some rs)
      | _ -> let _ = print_string "\n[lemproving.ml] error at process_lemma: list of coercions should have max length of 1 \n" in 
        (false, None)
    in
    (* let valid_l2r, rs_l2r = helper l2r check_left_coercion in    *)
    let valid_l2r, rs_l2r = (false, None) in
    let valid_r2l, rs_r2l = helper r2l check_right_coercion in
    let empty_resid = CF.FailCtx (CF.Trivial_Reason " empty residue") in
    let residues = match (rs_l2r, rs_r2l) with
      | (None, None) -> empty_resid
      | (None, Some rs) 
      | (Some rs, None) -> rs
      | (Some rs1, Some rs2) -> CF.list_context_union rs1 rs2
    in
    let valid = valid_l2r && valid_r2l in
    let num_id = "\nEntailing lemma \""^ coerc_name ^"\"" in
    if valid then 
      print_entail_result valid residues num_id
    else begin
      let num_id0, err_resid  = 
        match coerc_type with
          | I.Equiv -> begin
                if (valid_l2r == false) then
                  match rs_l2r with
                    | Some rs -> (" (left-to-right) ", rs)
                    | None -> (" (left-to-right) ",  empty_resid)
                else
                  match rs_r2l with
                    | Some rs -> (" (right-to-left) ", rs)
                    | None -> (" (right-to-left) ",  empty_resid)
            end
         | _ -> ("", residues) 
      in
      print_entail_result valid err_resid (num_id^num_id0)
    end;
  end
