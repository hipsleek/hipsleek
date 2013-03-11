open Globals
open Gen
open Cformula

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
let view_to_hprel_h_formula hf0=
  let rec helper hf=
    match hf with
      | CF.Star {h_formula_star_h1 = hf1;
              h_formula_star_h2 = hf2;
              h_formula_star_pos = pos} ->
          let n_hf1,hvs1 = helper hf1 in
          let n_hf2,hvs2 = helper hf2 in
          let new_hf=
            match n_hf1,n_hf2 with
              | (HEmp,HEmp) -> HEmp
              | (HEmp,_) -> n_hf2
              | (_,HEmp) -> n_hf1
              | _ -> (Star {h_formula_star_h1 = n_hf1;
                            h_formula_star_h2 = n_hf2;
                            h_formula_star_pos = pos})
          in
          (new_hf,hvs1@hvs2)
      | CF.Conj { h_formula_conj_h1 = hf1;
               h_formula_conj_h2 = hf2;
               h_formula_conj_pos = pos} ->
          let n_hf1,hvs1 = helper hf1 in
          let n_hf2,hvs2 = helper hf2 in
          (Conj { h_formula_conj_h1 = n_hf1;
                 h_formula_conj_h2 = n_hf2;
                 h_formula_conj_pos = pos},hvs1@hvs2)
      | CF.Phase { CF.h_formula_phase_rd = hf1;
                CF.h_formula_phase_rw = hf2;
                h_formula_phase_pos = pos} ->
          let n_hf1,hvs1 = helper hf1 in
          let n_hf2,hvs2 = helper hf2 in
          (CF.Phase { CF.h_formula_phase_rd = n_hf1;
                  CF.h_formula_phase_rw = n_hf2;
                  CF.h_formula_phase_pos = pos},hvs1@hvs2)
      | CF.DataNode hd -> (hf,[])
      | CF.ViewNode hv ->
          let eargs = List.map (fun v -> CP.mkVar v no_pos) (hv.CF.h_formula_view_node::hv.CF.h_formula_view_arguments) in
          let nh = CF.HRel (CP.SpecVar (HpT, hv.CF.h_formula_view_name, Unprimed ),eargs, no_pos) in
          (nh, [hv])
      | CF.HRel _
      | CF.Hole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp -> (hf,[])
  in
  helper hf0

let view_to_hprel_x (f0:CF.formula) : (CF.formula*CF.h_formula_view list)=
  let rec helper f2_f=
    match f2_f with
      | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
          let nf1,hvs1 = helper f1 in
          let nf2,hvs2 = helper f2 in
          (Or {formula_or_f1 = nf1 ; formula_or_f2 =  nf2 ; formula_or_pos = pos}, hvs1@hvs2)
      | Base b ->
          let nh,hvs= view_to_hprel_h_formula b.formula_base_heap in
          (Base { b with formula_base_heap =nh;}, hvs)
      | Exists b ->
          let nh,hvs = view_to_hprel_h_formula b.formula_exists_heap in
          (Exists {b with formula_exists_heap = nh;}, hvs)
  in
  helper f0

let view_to_hprel (f2_f:formula): (CF.formula*CF.h_formula_view list) =
  let pr1 hv= Cprinter.prtt_string_of_h_formula (CF.ViewNode hv) in
  let pr2 =pr_list pr1 in
  Debug.ho_1 "view_to_hprel" !print_formula (pr_pair !print_formula pr2)
      view_to_hprel_x f2_f

let norm_extract_common_one_view_x cprog cviews vdecl=
  let self_var = Cpure.SpecVar ((Named vdecl.C.view_data_name), self, Unprimed) in
  let hp = CP.SpecVar (HpT, vdecl.C.view_name, Unprimed) in
  let args = self_var::vdecl.C.view_vars in
  let unk_hps = [] in let unk_svl = [] in
  let cdefs = [] in
  let fs = CF.list_of_disjs (CF.struc_to_formula vdecl.C.view_formula) in
  (***views to hprels*******)
  let fs1 = List.map CF.elim_exists fs in
  let fs2,map = List.split (List.map view_to_hprel fs1) in
  let defs,ss = SAU.get_longest_common_hnodes_list cprog cdefs unk_hps unk_svl
    hp self_var vdecl.C.view_vars args fs2 in

  (***hprels to views*******)
  vdecl

let norm_extract_common_one_view cprog cviews vdecl=
  let pr1 = Cprinter.string_of_view_decl in
  Debug.ho_1 "norm_extract_common_one_view" pr1 pr1
      (fun _ -> norm_extract_common_one_view_x cprog cviews vdecl) vdecl

let norm_extract_common cprog cviews=
  let rec process_helper rem_vs done_vs=
    match rem_vs with
      | [] -> done_vs
      | vdecl::rest ->
          let n_vdecl = norm_extract_common_one_view cprog (done_vs@rest) vdecl in
          process_helper rest (done_vs@[n_vdecl])
  in
  process_helper cviews []

(*****************************************************************)
   (********EXTRACT common pattern **********)
(*****************************************************************)
