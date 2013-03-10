open Globals
open Gen

module DD = Debug
module CF=Cformula
module CP=Cpure
module MCP=Mcpure
module C = Cast
module SAU = Sautility

(***********************************************)
(*****ELIM unused parameters of view **********)
let norm_elim_useless_para_x cprog view_name sf args=
  let extract_svl f=
    let f1 = CF.elim_exists f in
    let new_f = CF.drop_view_formula f1 [view_name] in
    (* let _ = Debug.info_pprint (" new_f:" ^ (Cprinter.prtt_string_of_formula new_f) ) no_pos in *)
     (CF.fv new_f)
  in
  let rec build_keep_pos_list args res index all=
    match args with
      | [] -> res
      | a::ass -> if (CP.mem_svl a all) then
            build_keep_pos_list ass res (index+1) all
          else build_keep_pos_list ass (res@[index]) (index+1) all
   in
  if args = [] then (args,sf) else
    let svl = extract_svl (CF.struc_to_formula sf) in
    (* let _ = Debug.info_pprint (" svl:" ^ (!CP.print_svl svl) ) no_pos in *)
    (* let _ = Debug.info_pprint (" args:" ^ (!CP.print_svl args) ) no_pos in *)
    let new_args = CP.intersect_svl args svl in
    (* let _ = Debug.info_pprint (" new_args:" ^ (!CP.print_svl new_args) ) no_pos in *)
    if List.length args > List.length new_args then
      let keep_pos = build_keep_pos_list new_args [] 0 args in
      let n_sf = CF.drop_view_paras_struc_formula sf [(view_name,keep_pos)] in
      let dropped_args = CP.diff_svl args svl in
      let _ = Debug.info_pprint ("  ELIMINATE parameters:" ^ (!CP.print_svl dropped_args) ^ " of view " ^ view_name ^ "\n" ) no_pos in
      (new_args,n_sf)
    else
      (args,sf)

let norm_elim_useless_para cprog view_name sf args=
  let pr1 = Cprinter.string_of_struc_formula in
  Debug.no_2 "norm_elim_useless_para" pr1 !CP.print_svl (pr_pair !CP.print_svl pr1)
      (fun _ _ -> norm_elim_useless_para_x cprog view_name sf args) sf args

(***********************************************)
   (********EXTRACT common pattern **********)
(***********************************************)
let norm_extract_common_x cprog cviews vdecl=
  let self_var = Cpure.SpecVar ((Named vdecl.C.view_data_name), self, Unprimed) in
  let args = self_var::vdecl.C.view_vars in
  let unk_hps = [] in
  let cdefs = [] in
  let fs = fst (List.split vdecl.C.view_un_struc_formula) in
  if List.length fs <= 1 then
    vdecl
  else
    let lldns = List.map (fun f -> (SAU.get_hdnodes f, f)) fs in
    let min,sh_ldns,eqNulls,eqPures,hprels = SAU.get_min_common cprog args unk_hps lldns in
    if min = 0 && eqNulls = [] && eqPures= [] then vdecl else
      begin
          (* let orig_hpdefs, hp_subst, new_hp, n_args,sh_ldns2,next_roots = SAU.mk_orig_hprel_def cprog cdefs unk_hps hp r non_r_args args sh_ldns eqNulls eqPures hprels1 unk_svl in *)
          (* let n_fs = List.map (SAU.process_one_f cprog args n_args next_roots hp_subst sh_ldns2 eqNulls eqPures hprels1) lldns in *)
          (* let n_fs1 = List.filter (fun f -> not ((SAU.is_empty_f f) || (CF.is_only_neqNull n_args [] f))) n_fs in *)
          vdecl
      end

let norm_extract_common cprog cviews vdecl=
  let pr1 = Cprinter.string_of_view_decl in
  Debug.ho_1 "norm_extract_common" pr1 pr1
      (fun _ -> norm_extract_common_x cprog cviews vdecl) vdecl
