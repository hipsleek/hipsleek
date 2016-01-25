#include "xdebug.cppo"
open Globals
open Others
open Gen
open VarGen

open Cformula
open Satutil

module CP = Cpure
module CF = Cformula

let timeout = (10.0 : float)

let is_sat_pure_fnc_cex f = (let r = Tpdispatcher.is_sat_sub_no 21 f (ref 0) in (r,f))

let is_sat_pure_fnc f = Satutil.is_sat_pure_fnc f

let slsat_num = ref (0:int)
let slsat_unsat_num = ref (0:int)
let slsat_sat_num = ref (0:int)

let string_of_call_stk = pr_pair pr_id (pr_list string_of_int)

let get_path_ctl f=
  match (CF.get_path_trace f) with
    | None -> []
    | Some path_label ->
          (* List.fold_left (fun acc (_, ctl) -> if ctl == 0 then acc else *)
          (*   acc@[ctl] *)
          (* ) [] *) path_label

let string_of_path (a1,a2,a3,a4,a5,a6,a7,a8) =
  let pr1a vn = Cprinter.prtt_string_of_h_formula (ViewNode vn) in
  let pr1b = Cprinter.string_of_mix_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  (pr_hepta !CP.print_svl pr2 pr2 !CP.print_svl !CP.print_svl (pr_list pr1a) (pr_pair pr1b (pr_list string_of_call_stk)))
    (a1,a2,a3,a4,a5,a6,(a7,a8))

(**************************************** *)
(*******************SAT******************* *)
(**************************************** *)

(*****************************************)

let drop_all_views_h_formula hf0=
  let rec helper hf=
    match hf with
      | Star {h_formula_star_h1 = hf1;
              h_formula_star_h2 = hf2;
              h_formula_star_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          let new_hf=
            match n_hf1,n_hf2 with
              | (HEmp,HEmp) -> HEmp
              | (HEmp,_) -> n_hf2
              | (_,HEmp) -> n_hf1
              | _ -> (Star {h_formula_star_h1 = n_hf1;
                            h_formula_star_h2 = n_hf2;
                            h_formula_star_pos = pos})
          in
          (new_hf)
      | Conj { h_formula_conj_h1 = hf1;
               h_formula_conj_h2 = hf2;
               h_formula_conj_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          (Conj { h_formula_conj_h1 = n_hf1;
                 h_formula_conj_h2 = n_hf2;
                 h_formula_conj_pos = pos})
      | Phase { h_formula_phase_rd = hf1;
                h_formula_phase_rw = hf2;
                h_formula_phase_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          (Phase { h_formula_phase_rd = n_hf1;
                  h_formula_phase_rw = n_hf2;
                  h_formula_phase_pos = pos})
      | DataNode hd -> (hf)
      | ViewNode hv ->
            HEmp
      | ThreadNode _ -> (hf)
      | HRel _
      | Hole _ | FrmHole _
      | HTrue
      | HFalse
      | HEmp | HVar _ -> hf
      | StarMinus _ | ConjStar _ | ConjConj _ -> hf
  in
  helper hf0

let drop_all_views_formula (f0:formula) : formula=
  let rec helper f2_f=
    match f2_f with
      | Base b -> Base { b with formula_base_heap = drop_all_views_h_formula b.formula_base_heap;}
      | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
          Or ({formula_or_f1 = helper f1 ; formula_or_f2 =  helper f2 ; formula_or_pos = pos})
      | Exists b -> Exists {b with formula_exists_heap = drop_all_views_h_formula b.formula_exists_heap;}
  in
  helper f0


let unfold_one_view_x prog form_red_fnc (vnode:h_formula_view)=
  let vname = vnode.h_formula_view_name in
  let act_args = vnode.h_formula_view_node::vnode.h_formula_view_arguments in
  let caller_eqs, act_args1 = Satutil.fresh_dupl_svl act_args [] [] in
  let vdecl = Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls vname in
  let self_sv = if String.compare vdecl.Cast.view_data_name "" != 0 then
     CP.SpecVar (Named vdecl.Cast.view_data_name,self,Unprimed)
  else
    let p_root = List.hd act_args in
    let st = CP.type_of_spec_var p_root in
    try
      match st with
        | Named tname ->
              if String.compare tname "" != 0 then
                CP.SpecVar (st,self,Unprimed)
              else raise Not_found
        | _ -> (* raise Not_found *)
              CP.SpecVar (st,self,Unprimed)
    with _ -> begin
        try Cvutil.find_self_sv vdecl.Cast.view_un_struc_formula
        with _ -> CP.SpecVar (st,self,Unprimed)
    end
  in
  let sst = List.combine (self_sv::vdecl.Cast.view_vars) act_args1 in
  let fs = List.map (fun (f, _) -> subst sst f) vdecl.Cast.view_un_struc_formula in
  (*base case should be the first*)
  let base_fs, rec_fs = List.partition (fun f -> Cfutil.is_empty_heap_f f) fs in
  let fs1 = base_fs@rec_fs in
  let fs2 = match caller_eqs with
    | [] -> fs1
    | (sv11,sv12)::rest ->
          let p = List.fold_left (fun p (svi1,svi2) ->
              CP.mkAnd p (CP.mkPtrEqn svi1 svi2 no_pos) no_pos
          ) (CP.mkPtrEqn sv11 sv12 no_pos) rest
          in
          let mf = (MCP.mix_of_pure p) in
          List.map (fun f -> mkAnd_pure f mf no_pos) fs1
  in
  List.fold_left (fun r f ->
      let f0a = elim_exists f in
      let quans,f0b = split_quantifiers f0a in
      let fr_quans = CP.fresh_spec_vars quans in
      let f = subst (List.combine quans fr_quans) f0b in
      let (is_unsat,ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf) =
        form_red_fnc prog f in
      if is_unsat then r else
        let fname = try
          let idx = String.rindex vname '_' in
          String.sub vname 0 idx
        with Not_found -> vname
        in
        let pt = get_path_ctl f in
        r@[(ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf,[(fname,pt)])]
  ) [] (fs2)

let unfold_one_view prog form_red_fnc (vnode:h_formula_view)=
  let pr1a vn = Cprinter.prtt_string_of_h_formula (ViewNode vn) in
  let pr1b = Cprinter.string_of_mix_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 (a1,a2,a3,a4,a5,a6,a7,a8) = (pr_hepta ( !CP.print_svl) pr2 pr2 !CP.print_svl !CP.print_svl (pr_list pr1a) (pr_pair pr1b (pr_list string_of_call_stk)))
    (a1,a2,a3,a4,a5,a6,(a7,a8)) in
  Debug.no_1 "unfold_one_view" pr1a (pr_list_ln pr3)
      (fun _ -> unfold_one_view_x prog form_red_fnc vnode) vnode


(* let unfold_bfs_x prog (eqs0, neqs0, null_svl0, neqNull_svl0, hvs0, mf0) vns= *)
(*   (\* let f01 = (drop_all_views_formula f0) in *\) *)
(*   let ls_unfold_v_fs = List.map (fun vn -> unfold_one_view prog vn) vns in *)
(*   List.fold_left (fun ls vn_brs -> *)
(*       List.fold_left (fun r v_br -> *)
(*           r@(List.map (fun f -> mkStar_combine f v_br Flow_replace no_pos) ls) *)
(*       ) [] vn_brs *)
(*   ) [(eqs0, neqs0, null_svl0, neqNull_svl0, hvs0, mf0)] ls_unfold_v_fs *)

let unfold_bfs_x prog is_shape_only form_red_fnc is_inconsistent_fnc (ptos, eqs0, neqs0, null_svl0, neqNull_svl0, _, mf0, pt0) vns0=
  let combine_and_unsat_check unsat_caches (ptos1, eqs1, neqs1, null_svl1, neqNull_svl1, hvs1, mf1,pt1) (ptos2, eqs2, neqs2, null_svl2, neqNull_svl2, hvs2, mf2,pt2)=
    (* is conflict * on ptos *)
    if CP.intersect_svl ptos1 ptos2 != [] then [],unsat_caches else
      let ((ptos, eqs, neqs, null_svl, neqNull_svl, hvs,mf) (* as new_f *)) =
        combine_formula_abs is_shape_only (ptos1, eqs1, neqs1, null_svl1, neqNull_svl1, hvs1, mf1)
            (ptos2, eqs2, neqs2, null_svl2, neqNull_svl2, hvs2, mf2)
      in
      let is_unsat = is_inconsistent_fnc ptos eqs neqs null_svl neqNull_svl hvs mf in
      if is_unsat then ([],unsat_caches)
      else
        (* [(new_f)],unsat_caches *)
        ([(ptos, eqs, neqs, null_svl, neqNull_svl, hvs,mf, pt1@pt2)],unsat_caches)
  in
  let unfold_one_view_helper cur_disjs unfolded_vn_brs=
    List.fold_left (fun (acc_unfolded_fs, unsat_caches) ((ptos1, eqs1, neqs1, null_svl1, neqNull_svl1, hvs1, mf1, pt1) as br) -> (*each branch of vn*)
        let fs_br,new_unc2 = List.fold_left (fun (acc_unfolded_br_fs,unc1) ((ptos2, eqs2, neqs2, null_svl2, neqNull_svl2, hvs2, mf2,pt2) as unfolded_f)->
            (* combine with one current unfolded formula *)
            let new_disj,new_unsat_cache =(combine_and_unsat_check unc1  unfolded_f br) in
            acc_unfolded_br_fs@new_disj,new_unsat_cache
        ) ([],unsat_caches)  cur_disjs in
        acc_unfolded_fs@fs_br,new_unc2
    ) ([],[]) unfolded_vn_brs
  in
  let rec combine_eager_return disjs br unc1 res=
    match disjs with
      | disj::rest -> begin
          let new_disj,new_unsat_cache =(combine_and_unsat_check unc1 disj br) in
          match new_disj with
            | (_, _, _, _, _, hvs, _,_)::_ -> if hvs=[] then
                true, res@new_disj,new_unsat_cache
              else
                combine_eager_return rest br new_unsat_cache (res@new_disj)
            | _ -> combine_eager_return rest br new_unsat_cache (res@new_disj)
        end
      | [] -> false,res,unc1
  in
  (*like above but return the first sat*)
  let rec unfold_one_view_under_helper cur_disjs under_vn_brs res=
    match under_vn_brs with
      | [] -> false,res
      | vn_br::rest -> begin
            let is_sat,fs_br,new_unc2 = combine_eager_return cur_disjs vn_br [] [] in
            let new_res= (res@fs_br) in
            if is_sat then
              true,new_res
            else
              unfold_one_view_under_helper cur_disjs rest new_res
        end
  in
  (* *******************************)
  (* vn_1,..,vn_k
     (...(f_b AND unfold (vn_1)) AND ...) AND unfold (vn_k)
  *)
  let rec unfold_vn vns cur_disjs =
    match vns with
      | [vn] -> (* the last view. return the first sat if possible *)
            let unfolded_vn_brs = unfold_one_view prog (fun p f -> form_red_fnc p false f) vn in
        let under_vn_brs, over_vn_brs = List.partition (fun (_, _, _, _, _, hvs, _, _) -> hvs=[]) unfolded_vn_brs in
        let is_sat,unfolded_disjs_under = unfold_one_view_under_helper cur_disjs under_vn_brs [] in
        if is_sat then
          1, unfolded_disjs_under
        else
          let unfolded_disjs_over,_ = unfold_one_view_helper cur_disjs over_vn_brs in
          let unfolded_disjs = unfolded_disjs_under@unfolded_disjs_over in
          if unfolded_disjs = [] then 0,[] else
            2,unfolded_disjs
      | vn::rest ->
            let unfolded_vn_brs = unfold_one_view prog (fun p f -> form_red_fnc p true f) vn in
            let unfolded_disjs,_ =
              (* List.fold_left (fun (acc_unfolded_fs, unsat_caches) ((ptos1, eqs1, neqs1, null_svl1, neqNull_svl1, hvs1, mf1) as br) -> (\*each branch of vn*\) *)
              (*     let fs_br,new_unc2 = List.fold_left (fun (acc_unfolded_br_fs,unc1) ((ptos2, eqs2, neqs2, null_svl2, neqNull_svl2, hvs2, mf2) as unfolded_f)-> *)
              (*         (\* combine with one current unfolded formula *\) *)
              (*         let new_disj,new_unsat_cache =(combine_and_unsat_check unc1 br unfolded_f) in *)
              (*         acc_unfolded_br_fs@new_disj,new_unsat_cache *)
              (*     ) ([],unsat_caches)  cur_disjs in *)
              (*     acc_unfolded_fs@fs_br,new_unc2 *)
              (* ) ([],[]) unfolded_vn_brs *)
              unfold_one_view_helper cur_disjs unfolded_vn_brs
            in
            if unfolded_disjs = [] then 0,[] else
              unfold_vn rest unfolded_disjs
      | [] -> 2, cur_disjs
  in
  (* let view_args = CP.remove_dups_svl (List.fold_left (fun ls vn -> *)
  (*     ls@(vn.h_formula_view_arguments) *)
  (* ) [] vns0) in *)
  (* let mf1 = MCP.mix_of_pure (CP.filter_var (MCP.pure_of_mix mf0) view_args) in *)
  (* let ptos1 = CP.intersect_svl ptos view_args in *)
  (* let neqNull_svl1 = CP.intersect_svl neqNull_svl0 view_args in *)
  (* unfold_vn vns0 [(ptos1, eqs0, neqs0, null_svl0, neqNull_svl1, [], mf1)] *)

  unfold_vn vns0 [(ptos, eqs0, neqs0, null_svl0, neqNull_svl0, [], mf0, pt0)]

  (* let ls_unfold_v_fs = List.map (fun vn -> unfold_one_view prog vn) vns0 in *)
  (* let r = List.fold_left (fun ls vn_brs -> *)
  (*     List.fold_left (fun r (ptos1, eqs1, neqs1, null_svl1, neqNull_svl1, hvs1, mf1) -> *)
  (*         r@(List.fold_left (fun r2 (ptos2, eqs2, neqs2, null_svl2, neqNull_svl2, hvs2, mf2) -> *)
  (*             (\* is conflict * on ptos *\) *)
  (*             if CP.intersect_svl ptos1 ptos2 != [] then r2 else *)
  (*               let ((ptos, eqs, neqs, null_svl, neqNull_svl, hvs,mf) as new_f) = *)
  (*                 combine_formula_abs (ptos1, eqs1, neqs1, null_svl1, neqNull_svl1, hvs1, mf1) *)
  (*                 (ptos2, eqs2, neqs2, null_svl2, neqNull_svl2, hvs2, mf2) *)
  (*               in *)
  (*               let is_unsat = is_inconsistent ptos eqs neqs null_svl neqNull_svl in *)
  (*               if is_unsat then r2 else *)
  (*                 r2@[(new_f)] *)
  (*         ) [] ls) *)
  (*     ) [] vn_brs *)
  (* ) [(ptos, eqs0, neqs0, null_svl0, neqNull_svl0, [], mf0)] ls_unfold_v_fs *)
  (* in *)
  (* r=[],r *)

let unfold_bfs prog is_shape_only form_red_fnc is_inconsistent_fnc
      (ptos, eqs0, neqs0, null_svl0, neqNull_svl0, hvs0, mf0,pt0) vns=
  let pr1 = Cprinter.string_of_formula in
  let pr1a vn = Cprinter.prtt_string_of_h_formula (ViewNode vn) in
  let pr1b = Cprinter.string_of_mix_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr3 (a1,a2,a3,a4,a5,a6,a7,a8) = (pr_hepta !CP.print_svl pr2 pr2 !CP.print_svl !CP.print_svl (pr_list pr1a) (pr_pair pr1b (pr_list string_of_call_stk)))
    (a1,a2,a3,a4,a5,a6,(a7,a8)) in
  Debug.no_2 "unfold_bfs" pr3 (pr_list pr1a) (pr_pair string_of_int ( pr_list_ln pr3))
      (fun _ _ -> unfold_bfs_x prog is_shape_only form_red_fnc is_inconsistent_fnc
          (ptos, eqs0, neqs0, null_svl0, neqNull_svl0, hvs0, mf0,pt0) vns)
      (ptos, eqs0, neqs0, null_svl0, neqNull_svl0, hvs0, mf0,pt0) vns

(*
0: unsat
1: sat
2: unknown
*)
(* let rec check_sat_topdown_iter_x prog is_only_eq form_red_fnc is_inconsistent_fnc disjs0 count bound= *)
(*   let _ = DD.info_hprint (add_str "count" string_of_int) count no_pos in *)
(*   (\***************INTERNAL****************\) *)
(*   let rec find_first_sat disjs= *)
(*     match disjs with *)
(*       | [] -> None,[] *)
(*       | (ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf)::rest -> *)
(*             (\* let is_unsat, vns, mf = if is_only_eq then *\) *)
(*             (\*   form_red_eq prog f *\) *)
(*             (\* else form_red_all prog f *\) *)
(*             (\* in *\) *)
(*             (\* if not is_unsat then *\) *)
(*             (\*   (Some (f,vns), rest) *\) *)
(*             (\* else *\) *)
(*             (\*   find_first_sat rest *\) *)
(*             Some (ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf), rest *)
(*   in *)
(*   (\**************END*INTERNAL****************\) *)
(*   if count>=bound then 2 *)
(*   else *)
(*     let f_opt, rest_disjs = find_first_sat disjs0 in *)
(*     match f_opt with *)
(*       | None -> 0 *)
(*       | Some (ptos, eqs, neqs, null_svl, neqNull_svl, vns, mf) -> begin *)
(*           (\*is under-approximation - do not have any pred instances*\) *)
(*           if vns=[] then 1 else *)
(*             (\*unfold f*\) *)
(*             let idecided, new_disjs = unfold_bfs prog form_red_fnc is_inconsistent_fnc *)
(*               (ptos,eqs, neqs, null_svl, neqNull_svl, [], mf) vns in *)
(*             if idecided=1  then idecided else *)
(*               let acc_disjs = if idecided=0 then rest_disjs else (new_disjs@rest_disjs) in *)
(*               check_sat_topdown_iter prog is_only_eq form_red_fnc is_inconsistent_fnc acc_disjs (count+1) bound *)
(*         end *)

let rec check_sat_topdown_iter_x prog is_shape_only form_red_fnc is_inconsistent_fnc disjs0 count bound=
  let disjs_i = ref (disjs0) in
  let disjs_i_bk = ref (!disjs_i) in
  let disjs_i_plus = ref ([]) in
  let disjs_i_ind = ref ([]) in
  let disjs_i_minus_ind = ref ([]) in
  let count_i = ref (count) in
  let res = ref ((2, None)) in
  let finished = ref false in
  (***************INTERNAL****************)
  let rec find_first_sat disjs=
    match disjs with
      | [] -> None,[]
      | ((ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf,pt) as r)::rest ->
            (* let is_unsat, vns, mf = if is_only_eq then *)
            (*   form_red_eq prog f *)
            (* else form_red_all prog f *)
            (* in *)
            (* if not is_unsat then *)
            (*   (Some (f,vns), rest) *)
            (* else *)
            (*   find_first_sat rest *)
            (Some r (* (ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf, pt) *), rest)
  in
  let return lres=
    (* let _ = DD.info_hprint (add_str "lres" string_of_int) (lres) no_pos in *)
    let _ = res := lres in
    let _ = finished := true in
    ()
  in
  (**************END*INTERNAL****************)
  let _ = 
  while not !finished do
    let _ = DD.ninfo_hprint (add_str "count_i" string_of_int) (!count_i) no_pos in
    (* let pr1 = !CP.print_svl in *)
    (* let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
    (* let pr3 hv = (!print_h_formula (ViewNode hv)) in *)
    (* let pr4 = pr_list_ln (pr_hepta pr1 pr2 pr2 pr1 pr1 (pr_list pr3)  Cprinter.string_of_mix_formula) in *)
    (* let _ = DD.info_hprint (add_str "!disjs_i" pr4) (!disjs_i) no_pos in *)
    if !count_i>=bound then
      return (2, None)
    else
      let f_opt, rest_disjs = find_first_sat !disjs_i in
      match f_opt with
        | None -> return (0, None)
        | Some ((ptos, eqs, neqs, null_svl, neqNull_svl, vns, mf, pt) as f_j)-> begin
            (*is under-approximation - do not have any pred instances*)
            if vns=[] then
              let () = DD.ninfo_hprint (add_str "sat" (string_of_path)) f_j  no_pos in
              return (1, Some f_j)
            else
              (*unfold f*)
              let idecided, new_disjs = unfold_bfs prog is_shape_only form_red_fnc is_inconsistent_fnc
                (ptos,eqs, neqs, null_svl, neqNull_svl, [], mf, pt) vns in
              if idecided=1  then
                let _ = DD.ninfo_hprint (add_str "sat list" (pr_list_ln string_of_path)) new_disjs  no_pos in
                return (idecided, Some (List.hd new_disjs))
              else
                (* let acc_disjs = if idecided=0 then rest_disjs else *)
                (*   let _ = disjs_i_plus := !disjs_i_plus @ new_disjs in *)
                (*   (new_disjs@rest_disjs) *)
                (* in *)
                let _ = disjs_i := rest_disjs in
                (* if idecided=0 && rest_disjs=[] then () *)
                (* else *)
                  let _ =  disjs_i_ind := !disjs_i_ind@[f_j] in
                  let _ = disjs_i_plus := !disjs_i_plus @ new_disjs @ (!disjs_i) in
                  (* check_sat_topdown_iter prog is_only_eq form_red_fnc is_inconsistent_fnc acc_disjs (count+1) bound *)
                  if !disjs_i=[] then
                    let _ =
                      if !disjs_i_plus = [] then
                        return (0, None)
                      else
                        (* check fixpoint *)
                        if Satutil.checkeq_formula_list !disjs_i_minus_ind !disjs_i_ind then
                          return (0, None)
                        else
                          let _ = count_i := !count_i +1 in
                          let _ = disjs_i := !disjs_i_plus in
                          let _ = disjs_i_plus := [] in
                          let _ = disjs_i_minus_ind := !disjs_i_ind in
                          let _ = disjs_i_ind := [] in
                          ()
                    in ()
                  else ()
          end
  done
  in
  !res

and check_sat_topdown_iter prog is_shape_only form_red_fnc is_inconsistent_fnc disjs count bound=
  let pr1 = Cprinter.string_of_formula in
  let pr1a vn = Cprinter.prtt_string_of_h_formula (ViewNode vn) in
  let pr1b = Cprinter.string_of_mix_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  (* let pr3 = pr_list_ln (pr_hepta !CP.print_svl pr2 pr2 !CP.print_svl !CP.print_svl (pr_list pr1a) pr1b) in *)
  let pr3 = pr_list_ln string_of_path in
  let pr4 (_,_,_,_,_,_,_,pt) = (pr_list string_of_call_stk) pt in
  Debug.no_3 "check_sat_topdown_iter" pr3 string_of_int string_of_int (pr_pair string_of_int (pr_option pr4))
      (fun _ _ _ -> check_sat_topdown_iter_x prog is_shape_only form_red_fnc is_inconsistent_fnc disjs count bound)
      disjs count bound


let check_sat_topdown_x prog need_slice f0=
  (* print_endline_quiet "\n***slsat****"; *)
  let _ = DD.ninfo_hprint (add_str "f0" Cprinter.prtt_string_of_formula) f0 no_pos in
  let bound = 50000 in
  let is_shape_only,form_red_fnc, is_inconsistent_fnc =
    if not (!Globals.pred_has_pure_props) then
      true,form_red_eq, (is_inconsistent prog.Cast.prog_view_decls)
    else false,form_red_general, (is_inconsistent_general prog.Cast.prog_view_decls)
  in (*to combine with local infor of f0 for more precise*)
  (* let pure_sat_fnc p = is_sat_pure_fnc p in *)
  let check_sat_one_slice f=
    let (is_unsat,ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf) = 
      (* if is_only_eq then form_red_eq_fnc prog f else form_red_all prog f *)
      form_red_fnc prog true f
    in
    if is_unsat then (0, None) else
      check_sat_topdown_iter prog is_shape_only
          form_red_fnc is_inconsistent_fnc
          [(ptos, eqs, neqs, null_svl, neqNull_svl, hvs, mf, [])] 0 bound
  in
  let rec iter_slice_helper fs=
    match fs with
      | [] -> 1, None
      | f::rest ->
            let res1, cex = check_sat_one_slice f in
            if res1!=1 then (res1, cex) else
              iter_slice_helper rest
  in
  (* let f0a = elim_exists f0 in *)
  (* let quans,f1 = split_quantifiers f0a in *)
  (* let fs = if not need_slice ||  Cfutil.is_view_f f0 || not is_shape_only then [f0] *)
  (* else (Frame.heap_normal_form prog f0 Hgraph.hgraph_grp_min_size_unsat) *)
  (* in *)
  (* let res, cex = iter_slice_helper fs in *)
  let res, cex = check_sat_one_slice f0 in
  let _ = slsat_num := !slsat_num + 1 in
  let _ = if res=0 then slsat_unsat_num := !slsat_unsat_num + 1 else
    if res=1 then slsat_sat_num := !slsat_sat_num + 1 else ()
  in
  res,cex
  (* check_sat_one_slice f0 *)

let check_sat_topdown prog need_slice f=
  let pr1 = Cprinter.string_of_formula in
  let pr2 (_,_,_,_,_,_,_,pt) = (pr_list string_of_call_stk) pt in
  Debug.no_1 "check_sat_topdown" pr1 (pr_pair string_of_int (pr_option pr2))
      (fun _ -> check_sat_topdown_x prog need_slice f)
      f

(**************************************** *)
(**************************************** *)

let check_sat_exct_pure prog f=
  let b , cex = is_sat_pure_fnc_cex f in
  b,mk_cex2 b cex

let check_sat_under prog p hf=
  let b = true in
   b,mk_cex b

let check_unsat_over prog p_cex p hf=
  (* unfold hf until its pure <===> p_cex: hf_i *)
  (* do over approximate *)

  (* check unsat *)
  (* if unsat ==> terminate *)
  (* otherwise: return hf_i to find under *)
  true

let check_sat_ou_x prog count bound p hf=
(*
  if count <= bound then
  (* unsat of over *)
  let opt_unsat_hf_i = check_unsat_over prog p_cex p hf in
  match opt_unsat_hf_i with
   | None -> (*unsat*) b= false
   | Some hf_i -> let b, cex = check_sat_under prog p hf_i in
      if b then (b, cex) else
         (* add not cex into p *)
          let np = Cpure.mkAnd p (Cpure.mkNot cex.cex_model no_pos) no_pos in
          (* new iteration *)
          check_sat_ou prog (count+1) bound np hf
*)

  let b = true in
   b,mk_cex b

let check_sat_ou prog count bound p hf=
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = pr_pair string_of_bool Cprinter.string_of_failure_cex in
  let pr3 = string_of_int in
  Debug.no_4 "check_sat_ou" pr3 pr3 !Cpure.print_formula pr1 pr2
      (fun _ _ _ _ -> check_sat_ou_x prog count bound p hf)
      count bound p hf


(*
 hf is HEMP -> cex for pure
 don not have views -> exact xpure + cex for pure
 have views with all exact -> exact xpure + cex for pure
 otherwise
   over + under
*)
let check_sat_heap prog p hf0=
  (*all args are pointers*)
  let is_pointer_pred vname=
    try
      let vdef = Cast.look_up_view_def_raw x_loc prog.Cast.prog_view_decls vname in
      List.for_all CP.is_node_typ vdef.Cast.view_vars
    with _ -> false
  in
  let xpure_exact hf =
    let xp,_ = (Cvutil.expure_heap_symbolic prog hf 0 1) in
    let xp1 =  MCP.pure_of_mix xp in
    (* tranform pointers: x>0, x=1 -> x!=null *)
    let xp2 = Cputil.hloc_enum_to_symb xp1 in
    xp2
  in
  let rec recf hf= match hf with
    | HEmp -> check_sat_exct_pure prog p
    | _ ->
          let dnodes, vnodes,_ = get_hp_rel_h_formula hf in
          if vnodes = [] then
            let xp = xpure_exact hf in
            check_sat_exct_pure prog (CP.mkAnd p xp no_pos)
          else
            (*if user-defined pred are pointer-based*)
            let vnames = Gen.BList.remove_dups_eq (fun s1 s2 -> String.compare s1 s2 = 0)
              (List.fold_left (fun ls vn -> ls@[vn.h_formula_view_name]) [] vnodes) in
            if List.for_all is_pointer_pred vnames then
              let _ = Debug.ninfo_hprint (add_str "xxxx" pr_id) "2" no_pos in
              let xp = xpure_exact hf in
              check_sat_exct_pure prog (CP.mkAnd p xp no_pos)
            else
              let _ = Debug.info_hprint (add_str "xxxx" pr_id) "3" no_pos in
              check_sat_ou prog 0 10 p hf
  in
  recf hf0

(*
 f is HEMP -> cex
 don not have views -> cex
 have views with all exact -> cex
 otherwise
   over + under
*)
let check_sat_with_uo_x prog f0=
  let rec recf f= match f with
    | Cformula.Base fb -> check_sat_heap prog (Mcpure.pure_of_mix fb.formula_base_pure) fb.formula_base_heap
    | Cformula.Exists fe -> let _, bare = Cformula.split_quantifiers f in
      recf bare
    | Cformula.Or orf -> let bsat1, cex1 =  recf orf.formula_or_f1 in
      if bsat1 then bsat1, cex1
      else recf orf.formula_or_f2
  in
  recf f0

let check_sat_with_uo prog f=
  let pr1 = Cprinter.string_of_formula in
  let pr2 = pr_pair string_of_bool Cprinter.string_of_failure_cex in
  Debug.no_1 "check_sat_with_uo" pr1 pr2
      (fun _ -> check_sat_with_uo_x prog f) f

(* Loc: to implement*)
let check_imply_uo ante_uo conseq_uo=
  let is_sat = true in
  mk_cex is_sat

(* Loc: to implement*)
let check_imply_with_uo ante conseq=
  let is_sat = true in
  mk_cex is_sat

(* Loc: to implement*)
let check_sat_empty_rhs_with_uo_x es ante (conseq_p:CP.formula) matched_svl=
  let ante_pos = ante.formula_base_pos in
  (* let ante_w_fp = mkStar (Base ante) (formula_of_heap es.es_heap ante_pos) (Flow_combine) ante_pos in *)
  (* let is_sat = match ante.formula_base_heap with *)
  (*   | HEmp -> true *)
  (*   | _ -> false (\* to implement*\) *)
  (* in *)
  let is_sat = false in
  mk_cex is_sat

let check_sat_empty_rhs_with_uo es ante (conseq_p:CP.formula) matched_set=
  let pr1 = !print_formula_base in
  let pr2 = !CP.print_formula in
  Debug.no_4 "check_sat_empty_rhs_with_uo" Cprinter.string_of_entail_state pr1 pr2 !CP.print_svl Cprinter.string_of_failure_cex
      (fun _ _ _ _ -> check_sat_empty_rhs_with_uo_x es ante (conseq_p:CP.formula) matched_set)
      es ante conseq_p matched_set
