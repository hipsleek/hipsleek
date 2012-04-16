(*
  let $a = <formula>.
  let $b = compose.
  let $c = <formula>.
  
  Nested composition? How to perform the composition and keep the simplified result?
  
  let $a = compose ...
  let $b = compose[x]($a, ...).

  checkentail $a |- $b.
  What problem: not really, just do the composition.
  
  Is it better to keep the mapping as 
  var -> (CF.formula, IF.formula option)

  let $a = <formula>. --> translate with no quantification
  let $b = compose($a, ...) --> compose with no quantification, don't allow $b to be used in consequent position
  
  residue will not be used in consequent position.
*)

open Globals

module I = Iast
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure

module H = Hashtbl

exception SLEEK_Exception

type command =
  | DataDef of I.data_decl
  | PredDef of I.view_decl
  | FuncDef of I.func_decl
  | RelDef of I.rel_decl (* An Hoa *)
  | AxiomDef of I.axiom_decl (* [4/10/2011] An Hoa *)
  | LemmaDef of I.coercion_decl
  | LetDef of (ident * meta_formula)
  | EntailCheck of (meta_formula * meta_formula)
  | Infer of (ident list * meta_formula * meta_formula)
  | CaptureResidue of ident
  | PrintCmd of print_cmd
  | Time of (bool*string*loc)
  | EmptyCmd 

and print_cmd =
  | PVar of ident
  | PCmd of ident
	  
and meta_formula =
  | MetaVar of ident
  | MetaForm of IF.formula
  | MetaFormCF of CF.formula
  | MetaFormLCF of CF.list_formula
  | MetaEForm of Iformula.struc_formula
  | MetaEFormCF of CF.struc_formula
  | MetaCompose of (ident list * meta_formula * meta_formula)

(*
  The second component is IF.formula and not CF.formula since
  depending on how the formula is used (in negative or positive
  position of an entailment), it will get translated differently.
  Therefore we keep the original version and do the translations
  according to different usage.
*)

type var_table_t = (ident, meta_formula) H.t

let var_tab : var_table_t = H.create 10240

let string_of_command c = match c with
  | DataDef _ -> "DataDef"
  | PredDef _ -> "PredDef" 
  | FuncDef  _ -> "FuncDef"  
  | RelDef  _ -> "RelDef"  
  | AxiomDef  _ -> "AxiomDef"  
  | LemmaDef  _ -> "LemmaDef"
  | LetDef  _ -> "LetDef"   
  | EntailCheck _ -> "EntailCheck"
  | Infer _ -> "Infer"
  | CaptureResidue _ -> "CaptureResidue"  
  | PrintCmd _ -> "PrintCmd"  
  | Time _ -> "Time"
  | EmptyCmd -> "EmptyCmd"

let put_var (v : ident) (info : meta_formula) = H.add var_tab v info

let get_var (v : ident) : meta_formula = H.find var_tab v

(* An Hoa : String representation of meta_formula *)
let string_of_meta_formula (mf : meta_formula) = 
	match mf with
  | MetaVar i -> i
  | MetaForm f -> "IFORM:"^Iprinter.string_of_formula f
  | MetaFormCF cf ->  "CFORM:"^Cprinter.string_of_formula cf
  | MetaFormLCF lf -> "" (* TODO Implement *)
  | MetaEForm sf -> "IFORMStruc:"^Iprinter.string_of_struc_formula sf
  | MetaEFormCF sf -> "CFORMStruc:"^Cprinter.string_of_struc_formula sf
  | MetaCompose _ -> "" (* TODO Implement *)

let clear_var_table () = H.clear var_tab

(*
  let get_var (v : ident) : let_body =
  H.find var_tab v
  
  let put_var (v : ident) (body : let_body) =
  H.add var_tab v body
  
  let formula_of_var (v : ident) pos : IF.formula =
  let lbody = get_var v in
  match lbody with
  | LetForm lf -> lf
  | 
*)

let rec attach_htrue_to_meta_formula (metaform: meta_formula) : meta_formula =
  let rec attach_htrue_to_iformula (iform: IF.formula) : IF.formula = (
    match iform with
    | IF.Base base_form ->
        let pos = base_form.IF.formula_base_pos in
        let heap = base_form.IF.formula_base_heap in 
        let new_heap = IF.mkStar heap IF.HTrue pos in
        let new_base_form = { base_form with IF.formula_base_heap = new_heap } in
        IF.Base new_base_form
    | IF.Exists exist_form ->
        let pos = exist_form.IF.formula_exists_pos in
        let heap = exist_form.IF.formula_exists_heap in
        let new_heap = IF.mkStar heap IF.HTrue pos in
        let new_exists_form = { exist_form with IF.formula_exists_heap = new_heap } in
        IF.Exists new_exists_form
    | IF.Or or_form ->
        let f1 = or_form.IF.formula_or_f1 in
        let new_f1 = attach_htrue_to_iformula f1 in
        let f2 = or_form.IF.formula_or_f2 in
        let new_f2 = attach_htrue_to_iformula f2 in
        let new_or_form = { or_form with IF.formula_or_f1 = new_f1;
                                         IF.formula_or_f2 = new_f2; } in
        IF.Or new_or_form
  ) 
  and attach_htrue_to_cformula (cform: CF.formula) : CF.formula = (
    match cform with
    | CF.Base base_form ->
        let pos = base_form.CF.formula_base_pos in
        let heap = base_form.CF.formula_base_heap in 
        let new_heap = CF.mkStarH heap CF.HTrue pos in
        let new_base_form = { base_form with CF.formula_base_heap = new_heap } in
        CF.Base new_base_form
    | CF.Exists exist_form ->
        let pos = exist_form.CF.formula_exists_pos in
        let heap = exist_form.CF.formula_exists_heap in
        let new_heap = CF.mkStarH heap CF.HTrue pos in
        let new_exists_form = { exist_form with CF.formula_exists_heap = new_heap } in
        CF.Exists new_exists_form
    | CF.Or or_form ->
        let f1 = or_form.CF.formula_or_f1 in
        let new_f1 = attach_htrue_to_cformula f1 in
        let f2 = or_form.CF.formula_or_f2 in
        let new_f2 = attach_htrue_to_cformula f2 in
        let new_or_form = { or_form with CF.formula_or_f1 = new_f1;
                                         CF.formula_or_f2 = new_f2; } in
        CF.Or new_or_form
  )
  and attach_htrue_to_struc_iformula (struc_form : IF.struc_formula) : IF.struc_formula = (
    match struc_form with
    | IF.ECase struc_case ->
        let attach_true_to_branch (branch: IP.formula * IF.struc_formula) : (IP.formula * IF.struc_formula) =
          let f = fst branch in 
          let sf = snd branch in
          let new_sf = attach_htrue_to_struc_iformula sf in
          let new_branch = (f, new_sf) in
          new_branch in
        let branches = struc_case.IF.formula_case_branches in
        let new_branches = List.map attach_true_to_branch branches in
        let new_struc_case = { struc_case with IF.formula_case_branches = new_branches } in
        IF.ECase new_struc_case
    | IF.EBase struc_base ->
        let base = struc_base.IF.formula_struc_base in
        let new_base = attach_htrue_to_iformula base in
        let cont = struc_base.IF.formula_struc_continuation in
        let new_cont = match cont with
          | None -> None
          | Some sf -> Some (attach_htrue_to_struc_iformula sf) in
        let new_struc_base = {struc_base with IF.formula_struc_base = new_base;
                                              IF.formula_struc_continuation = new_cont } in
        IF.EBase new_struc_base
    | IF.EAssume (form, form_lb) ->
        let new_form = attach_htrue_to_iformula form in
        IF.EAssume (new_form, form_lb)
    | IF.EInfer struc_infer ->
        let cont = struc_infer.IF.formula_inf_continuation in
        let new_cont = attach_htrue_to_struc_iformula cont in
        let new_struc_infer = {struc_infer with IF.formula_inf_continuation = new_cont } in
        IF.EInfer new_struc_infer
    | IF.EList struc_list ->
        let attach_htrue_to_item (item: Label_only.spec_label_def * IF.struc_formula) 
                                : (Label_only.spec_label_def * IF.struc_formula) =
          let sld = fst item in
          let sf = snd item in
          let new_sf = attach_htrue_to_struc_iformula sf in
          (sld, new_sf) in
        let new_struc_list = List.map attach_htrue_to_item struc_list in
        IF.EList new_struc_list
    | IF.EOr struc_or -> 
        let sf1 = struc_or.IF.formula_struc_or_f1 in
        let sf2 = struc_or.IF.formula_struc_or_f2 in
        let new_sf1 = attach_htrue_to_struc_iformula sf1 in
        let new_sf2 = attach_htrue_to_struc_iformula sf2 in
        let new_struc_or = { struc_or with IF.formula_struc_or_f1 = new_sf1;
                                           IF.formula_struc_or_f2 = new_sf2; } in
        IF.EOr new_struc_or
  )
  and attach_htrue_to_struc_cformula (struc_form : CF.struc_formula) : CF.struc_formula = (
    match struc_form with
    | CF.ECase struc_case ->
        let attach_true_to_branch (branch: CP.formula * CF.struc_formula) : (CP.formula * CF.struc_formula) =
          let f = fst branch in 
          let sf = snd branch in
          let new_sf = attach_htrue_to_struc_cformula sf in
          let new_branch = (f, new_sf) in
          new_branch in
        let branches = struc_case.CF.formula_case_branches in
        let new_branches = List.map attach_true_to_branch branches in
        let new_struc_case = { struc_case with CF.formula_case_branches = new_branches } in
        CF.ECase new_struc_case
    | CF.EBase struc_base ->
        let base = struc_base.CF.formula_struc_base in
        let new_base = attach_htrue_to_cformula base in
        let cont = struc_base.CF.formula_struc_continuation in
        let new_cont = match cont with
          | None -> None
          | Some sf -> Some (attach_htrue_to_struc_cformula sf) in
        let new_struc_base = {struc_base with CF.formula_struc_base = new_base;
                                              CF.formula_struc_continuation = new_cont } in
        CF.EBase new_struc_base
    | CF.EAssume (spvars, form, form_lb) ->
        let new_form = attach_htrue_to_cformula form in
        CF.EAssume (spvars, new_form, form_lb)
    | CF.EInfer struc_infer ->
        let cont = struc_infer.CF.formula_inf_continuation in
        let new_cont = attach_htrue_to_struc_cformula cont in
        let new_struc_infer = {struc_infer with CF.formula_inf_continuation = new_cont } in
        CF.EInfer new_struc_infer
    | CF.EList struc_list ->
        let attach_htrue_to_item (item: Label_only.spec_label_def * CF.struc_formula) 
                                : (Label_only.spec_label_def * CF.struc_formula) =
          let sld = fst item in
          let sf = snd item in
          let new_sf = attach_htrue_to_struc_cformula sf in
          (sld, new_sf) in
        let new_struc_list = List.map attach_htrue_to_item struc_list in
        CF.EList new_struc_list
    | CF.EOr struc_or -> 
        let sf1 = struc_or.CF.formula_struc_or_f1 in
        let sf2 = struc_or.CF.formula_struc_or_f2 in
        let new_sf1 = attach_htrue_to_struc_cformula sf1 in
        let new_sf2 = attach_htrue_to_struc_cformula sf2 in
        let new_struc_or = { struc_or with CF.formula_struc_or_f1 = new_sf1;
                                           CF.formula_struc_or_f2 = new_sf2; } in
        CF.EOr new_struc_or
  ) 
  and attach_htrue_to_compose (compose : ident list * meta_formula * meta_formula) = (
    let (il, mf1, mf2) = compose in
    let new_mf1 = attach_htrue_to_meta_formula mf1 in
    let new_mf2 = attach_htrue_to_meta_formula mf2 in
    (il, new_mf1, new_mf2)
  ) in
  let new_metaform = match metaform with
    | MetaVar _ -> metaform
    | MetaForm iform -> MetaForm (attach_htrue_to_iformula iform)
    | MetaFormCF cform -> MetaFormCF (attach_htrue_to_cformula cform)
    | MetaFormLCF lcform -> 
        let new_lcfrom = List.map attach_htrue_to_cformula lcform in 
        MetaFormLCF new_lcfrom
    | MetaEForm struc_iform -> MetaEForm (attach_htrue_to_struc_iformula struc_iform)
    | MetaEFormCF struc_cform -> MetaEFormCF (attach_htrue_to_struc_cformula struc_cform)
    | MetaCompose compose -> MetaCompose (attach_htrue_to_compose compose) in
  new_metaform