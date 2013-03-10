open Globals
open Gen

module DD = Debug
module CF=Cformula
module CP=Cpure
module MCP=Mcpure
module C = Cast

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
      (new_args,n_sf)
    else
      (args,sf)

let norm_elim_useless_para cprog view_name sf args=
  let pr1 = Cprinter.string_of_struc_formula in
  Debug.no_2 "norm_elim_useless_para" pr1 !CP.print_svl (pr_pair !CP.print_svl pr1)
      (fun _ _ -> norm_elim_useless_para_x cprog view_name sf args) sf args

(***********************************************)
