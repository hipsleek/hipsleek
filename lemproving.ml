open Globals

module AS = Astsimp
module C  = Cast
module CF = Cformula
module CP = Cpure


let run_entail_check ante conseq = 
  let rs = (CF.FailCtx (CF.Trivial_Reason " exception in lemma proving ")) in
  (false, rs)


let print_exc (check_id: string) =
  Printexc.print_backtrace stdout;
  dummy_exception() ; 
  print_string ("exception in " ^ check_id ^ " check\n")

let process_lemma_check (iante0 : Sleekcommons.meta_formula) (iconseq0 : Sleekcommons.meta_formula) (lemma_name: string) =
  try 
    run_entail_check iante0 iconseq0
  with _ -> print_exc ("lemma \""^ lemma_name ^"\""); 
      let rs = (CF.FailCtx (CF.Trivial_Reason " exception in lemma proving ")) in
      (false, rs)

let process_lemma_check (iante0 :Sleekcommons.meta_formula) (iconseq0 : Sleekcommons.meta_formula) (lemma_name: string) =
  let pr = Sleekcommons.string_of_meta_formula in
  Gen.Debug.no_2 "process_lemma_check" pr pr (fun _ -> "?") (fun _ _ -> process_lemma_check iante0 iconseq0 lemma_name) iante0 iconseq0

let check_coercion coer lhs (rhs:CF.formula) cprog =
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
    process_lemma_check (Sleekcommons.MetaFormCF lhs) (Sleekcommons.MetaFormCF rhs) coer.C.coercion_name

let check_coercion coer lhs rhs cprog =
  let pr1 = Cprinter.string_of_coercion in
  let pr2 = Cprinter.string_of_formula in
  Gen.Debug.no_3 "check_coercion" pr1 pr2 pr2 (fun (valid,rs) -> string_of_bool valid) (fun _ _ _ -> check_coercion coer lhs rhs cprog ) coer lhs rhs

(* below expects struc_formula for rhs *)
let check_coercion_struc coer lhs rhs cprog =
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
    process_lemma_check (Sleekcommons.MetaFormCF lhs) (Sleekcommons.MetaEFormCF rhs) coer.C.coercion_name

let check_left_coercion coer cprog =
  let ent_lhs =coer.C.coercion_head in
  let ent_rhs = coer.C.coercion_body_norm in
  check_coercion_struc coer ent_lhs ent_rhs cprog

let check_right_coercion coer cprog =
  let ent_rhs = coer.C.coercion_head_norm in
  let ent_lhs = coer.C.coercion_body in
  check_coercion coer ent_lhs ent_rhs cprog


let process_lemma (l2r: C.coercion_decl list) (r2l: C.coercion_decl list) (cprog: C.prog_decl) =
  if !Globals.check_coercions then begin
    let helper coercs check_coerc = match coercs with
      | [] -> (true, None)
      | coerc::[] -> let (valid, rs) = check_coerc coerc cprog in (valid, Some rs)
      | _ -> let _ = print_string "\n[sleekengine.ml] error at process_lemma: list of coercions should have max length of 1 \n" in 
        (false, None)
    in
    let valid_l2r, rs_l2r = helper l2r check_left_coercion in
    let valid_r2l, rs_r2l = helper r2l check_right_coercion in
    let empty_resid = CF.FailCtx (CF.Trivial_Reason " empty residue") in
    let residues = match (rs_l2r, rs_r2l) with
      | (None, None) -> empty_resid
      | (None, Some rs) 
      | (Some rs, None) -> rs
      | (Some rs1, Some rs2) -> CF.list_context_union rs1 rs2
    in
    let valid = valid_l2r && valid_r2l in
    let num_id = "\nEntailing lemma \""^ (ldef.I.coercion_name) ^"\"" in
    if valid then 
      print_entail_result valid residues num_id
    else begin
      let num_id0, err_resid  = 
        match ldef.I.coercion_type with
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
