#include "xdebug.cppo"
open VarGen
open Globals
open Others
open Gen
open Cformula

module DD = Debug
module Err = Error
module CA = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module TP = Tpdispatcher
(* module SAU = Sautility *)


type iaction =
  | I_infer_dang
  (* | I_pre_trans_closure *)
  | I_split_base
  | I_partition (* pre, pre-oblg, post, post-oblg *)
  | I_pre_synz of (CP.spec_var list * CF.hprel list)
  | I_pre_fix of ( CP.spec_var list)
  | I_pre_oblg
  | I_post_synz
  | I_post_fix of ( CP.spec_var list)
  | I_post_oblg
  | I_seq of iaction_wt list

and iaction_wt = (int * iaction)
(* -1 : unknown, 0 : mandatory; >0 : optional (lower value has higher priority) *)


let rec string_of_iaction act=
  match act with
    | I_infer_dang -> "analize dangling"
    (* | I_pre_trans_closure -> "find transitive closure" *)
    | I_split_base ->  "split base"
    | I_partition -> "pre, pre-oblg, post, post-oblg"
    | I_pre_synz (hps,_) -> ("(pre) synthesize:" ^ (!CP.print_svl hps))
    | I_pre_fix hps -> ("(pre fix) synthesize:" ^ (!CP.print_svl hps))
    | I_pre_oblg -> "pre-oblg"
    | I_post_synz -> "post-preds synthesize"
    | I_post_fix hps -> ("(post fix) synthesize:" ^ (!CP.print_svl hps))
    | I_post_oblg -> "post-oblg"
    | I_seq ls_act -> "seq:" ^ (String.concat ";" (List.map (pr_pair string_of_int string_of_iaction) ls_act))

let mk_is constrs all_constrs link_hpargs dang_hpargs unk_map sel_hps post_hps cond_path iflow
      hp_equivs hpdefs=
  {
      is_constrs = constrs; (*current process constraints*)
      is_all_constrs = all_constrs; (* constraints*)
      is_link_hpargs = link_hpargs;
      is_dang_hpargs = dang_hpargs; (*dangling hps == link hps = unknown. to remove one of them*)
      is_sel_hps = sel_hps;
      is_unk_map = unk_map;
      is_post_hps = post_hps;
      is_prefix_hps = [];
      is_cond_path = cond_path;
      is_flow = iflow;
      is_hp_equivs = hp_equivs;
      is_hp_defs = hpdefs;
  }

let icompute_action_init need_preprocess detect_dang=
  let pre_acts=
    if need_preprocess then
      let dang_act =
        if detect_dang then
          [(0, I_infer_dang)]
        else []
      in
      dang_act@[(0, I_split_base)]
    else
      []
  in
  I_seq (pre_acts@[(0, I_partition)])


(*
That means the following priorities:
   0. H(...) & p -> emp
   1. H(..) --> H2(..)
   2. H(..) | G --> H2(..)
   3. H(..) * D --> H2(..)
   4. H(..)  --> D*H2(..)
*)
let ranking_frozen_mutrec_preds_x pr_hp_cs=
  let pre_preds_4_equal_w_prio = List.map (fun (hp,cs,deps) ->
      let is_lhs_emp = (CF.extract_hrel_head cs.CF.hprel_lhs <> None) in
      let is_rhs_emp = (CF.extract_hrel_head cs.CF.hprel_rhs <> None) in
      let is_pure = try
        let todo_unk = CF.extract_HRel_f cs.CF.hprel_lhs in
        Sautil.is_empty_f cs.CF.hprel_rhs
      with _ -> false
      in
      let is_empty_both = is_lhs_emp && is_rhs_emp (*&& (deps=[]) *) in
      let is_guard = (cs.CF.hprel_guard <> None) && is_rhs_emp in
      (hp,cs, is_pure, is_empty_both, is_guard, (not is_lhs_emp) && is_rhs_emp , CF.get_h_size_f cs.CF.hprel_rhs)
  )
    pr_hp_cs
  in
  let pr1 = Cprinter.string_of_hprel_short in
  let pr2 = pr_list_ln (pr_hepta !CP.print_sv pr1 string_of_bool string_of_bool string_of_bool string_of_bool
      string_of_int
  ) in
  let () = Debug.ninfo_zprint  (lazy  ("    pre_preds_4_equal_w_prio: " ^ ((pr2) pre_preds_4_equal_w_prio))) no_pos in
  (*first ranking*)
  (* let pure_ls = List.filter (fun (_,_, is_pure,_, _, _ , _) ->  is_pure) pre_preds_4_equal_w_prio in *)
  (* match pure_ls with *)
  (*   | (hp,cs,_,_,_,_,_)::_ -> [(hp,[cs])] *)
  (*   | _ -> *) begin
        let fst_ls = List.filter (fun (_,_,_, is_empty_both, _, _ , _) ->  is_empty_both) pre_preds_4_equal_w_prio in
        let () = Debug.ninfo_zprint  (lazy  ("    fst_ls: " ^ ((pr2) fst_ls))) no_pos in
        match fst_ls with
          | (hp,cs,_,_,_,_,_)::_ -> [(hp,[cs])]
          | _ -> begin
              let snd_ls = List.filter (fun (_,_,_, _, is_guard, _ , _) ->  is_guard) pre_preds_4_equal_w_prio in
              match snd_ls with
                | (hp,cs,_,_,_,_,_)::_ -> [(hp,[cs])]
                | _ -> begin
                    let rd_ls = List.filter (fun (_, _,_, _, _, is_emp_r , _) ->  is_emp_r) pre_preds_4_equal_w_prio in
                    match rd_ls with
                      | (hp,cs,_,_,_,_,_)::_ -> [(hp,[cs])]
                      | _ -> begin
                          let hp,cs,_,_,_,_,_ = List.fold_left (fun (hp0,cs0,a, a0,b0,c0, s0) (hp1,cs1,b, a1,b1,c1, s1) ->
                              if s1<s0 then (hp1,cs1,b, a1,b1,c1, s1) else (hp0,cs0,a,a0, b0, c0, s0)
                          ) (List.hd pre_preds_4_equal_w_prio) (List.tl pre_preds_4_equal_w_prio) in
                          [(hp,[cs])]
                        end
                  end
            end
      end

let ranking_frozen_mutrec_preds pr_hp_cs=
  let pr1 = Cprinter.string_of_hprel_short in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv (pr_list_ln pr1)) in
  let pr3 = pr_list_ln (pr_triple !CP.print_sv pr1 !CP.print_svl) in
  Debug.no_1 "ranking_frozen_mutrec_preds" pr3 pr2
      (fun _ -> ranking_frozen_mutrec_preds_x pr_hp_cs)
      pr_hp_cs

(*
  find all pre-preds that has only one assumption ===> equal
*)
let icompute_action_pre_x constrs post_hps frozen_hps pre_fix_hps=
  let ignored_hps = post_hps@frozen_hps@pre_fix_hps in
  let partition_pre_preds (pre_preds, rem_constrs, tupled_hps) cs=
    let l_hpargs = CF.get_HRels_f cs.CF.hprel_lhs in
    let r_hpargs = CF.get_HRels_f cs.CF.hprel_rhs in
    let rhps = List.map fst r_hpargs in
    match l_hpargs with
      | [] -> (pre_preds, rem_constrs@[cs],tupled_hps)
      | [(hp,_)] -> if CP.mem_svl hp ignored_hps then (pre_preds, rem_constrs@[cs],tupled_hps)
        else
         (pre_preds@[(hp,cs, CP.diff_svl rhps (ignored_hps))],rem_constrs,tupled_hps)
      | _ -> let linter = List.fold_left (fun ls (hp,args) ->
            if not (CP.mem_svl hp ignored_hps) && List.exists (fun (_,args1) ->
                Sautil.eq_spec_var_order_list args args1
            ) r_hpargs then
              ls@[hp]
            else ls
        ) [] l_hpargs in
            if linter  = [] then (pre_preds, rem_constrs@[cs], tupled_hps@(List.map fst l_hpargs))
            else
              (pre_preds@(List.map (fun hp -> (hp,cs, CP.diff_svl rhps (ignored_hps))) linter), rem_constrs,tupled_hps)
  in
  let check_is_guard cs = match cs.CF.hprel_guard with
    | None -> false
    | Some _ -> true
  in
  (* let pr1 = Cprinter.string_of_hprel_short in *)
  let rec partition_equal (cand_equal, complex_nrec_ndep, complex_non_rec, complex_hps) ls_pre=
   match ls_pre with
     | [] -> (cand_equal, complex_nrec_ndep, complex_non_rec, complex_hps)
     | (hp0, cs0, dep_hps0)::rest ->
           (* let () = Debug.info_zprint  (lazy  ("   cs0: " ^ (pr1 cs0))) no_pos in *)
           let () = Debug.ninfo_zprint  (lazy  ("   hp0: " ^ (!CP.print_sv hp0))) no_pos in
           let is_rec, is_guard, dep_hps, grp,rest1 = List.fold_left (fun (r_rec,r_guard, r_deps, ls1,ls2) (hp1,cs1,dep_hps1) ->
               (* let () = Debug.info_zprint  (lazy  ("   cs1: " ^ (pr1 cs1))) no_pos in *)
               if CP.eq_spec_var hp1 hp0 then
                 (r_rec || CP.mem_svl hp1 dep_hps1, r_guard || ( check_is_guard cs1), r_deps@dep_hps1,  ls1@[cs1], ls2)
               else
                 (r_rec, r_guard,r_deps, ls1, ls2@[(hp1,cs1,dep_hps1)])
           ) (CP.mem_svl hp0 dep_hps0,  check_is_guard cs0, dep_hps0, [],[]) rest in
           let grp1 = (cs0::grp) in
           (* let () = Debug.info_zprint  (lazy  ("   is_guard: " ^ (string_of_bool is_guard))) no_pos in *)
           (* let () = Debug.info_zprint  (lazy  ("   is_rec: " ^ (string_of_bool is_rec))) no_pos in *)
           (*has more than one constraints: disj but not recursive also join the race*)
           let n_res = if List.length grp1 > 1 then
             if not is_rec && is_guard then
               (* let () = Debug.info_pprint ("   0: ") no_pos in *)
               (cand_equal, complex_nrec_ndep, complex_non_rec@[(hp0,grp1)], complex_hps)
             else if  not is_rec && dep_hps = [] then
               (cand_equal, complex_nrec_ndep@[(hp0,grp1)], complex_non_rec, complex_hps)
             else
               (* let () = Debug.info_pprint ("   1: ") no_pos in *)
               (cand_equal, complex_nrec_ndep, complex_non_rec, complex_hps@[hp0])
           else
             if is_guard then
               (* let () = Debug.info_pprint ("   2: ") no_pos in *)
               (cand_equal, complex_nrec_ndep, complex_non_rec@[(hp0,grp1)], complex_hps)
             else if is_rec then
               (* let () = Debug.info_pprint ("   3: ") no_pos in *)
               (cand_equal, complex_nrec_ndep, complex_non_rec, complex_hps@[hp0])
             else
               (* let () = Debug.info_pprint ("   4: ") no_pos in *)
               (cand_equal@[(hp0,cs0, dep_hps0)],complex_nrec_ndep, complex_non_rec, complex_hps)
           in
           partition_equal n_res rest1
  in
  (* let is_pure_guard (hp0, grp) = *)
  (*   let fs, ogs = List.fold_left (fun (r1,r2) cs -> (cs.CF.hprel_rhs::r1, cs.CF.hprel_guard::r2)) ([],[]) grp in *)
  (*   if List.exists (fun og -> *)
  (*       match og with *)
  (*         | None -> false *)
  (*         | Some f -> not (CP.isConstTrue (CF.get_pure f)) *)
  (*   ) ogs then *)
  (*     let hps = List.fold_left (fun r f -> r@(CF.get_hp_rel_name_formula f)) [] fs in *)
  (*     CP.diff_svl hps [hp0] <> [] *)
  (*   else false *)
  (* in *)
  (************END************)
  (*tupled_hps: will be processed as pre-oblg *)
  let pr_pre_preds, _, tupled_hps = List.fold_left partition_pre_preds ([],[],[]) constrs in
  let pre_preds_cand_equal0, complex_nrec_ndep, complex_nonrec_guard_grps, complex_hps =
    partition_equal ([],[],[],[]) pr_pre_preds
  in
  let pr2 (a,_,_) = !CP.print_sv a in
  let () = Debug.ninfo_zprint  (lazy  ("    pre_preds_cand_equal0: " ^ ((pr_list pr2) pre_preds_cand_equal0))) no_pos in
  let () = Debug.ninfo_zprint  (lazy  ("    tupled_hps: " ^ (!CP.print_svl tupled_hps))) no_pos in
  (*filter the tupled_hps *)
  let pre_preds_cand_equal1 = List.filter (fun (hp,_,_) -> not (CP.mem_svl hp tupled_hps)) pre_preds_cand_equal0 in
  let () = Debug.ninfo_zprint  (lazy  ("    pre_preds_cand_equal1: " ^ ((pr_list pr2) pre_preds_cand_equal1))) no_pos in
  (*filter frozen candidates that depends on others. they will be synthesized next round.*)
  (* let cand_equal_hps = List.map fst3 pre_preds_cand_equal1 in *)
  let nonrec_complex_guard_hps = List.map fst complex_nonrec_guard_grps in
  (*remove one that depends on the guard, the guard should go first*)
  let () = Debug.ninfo_zprint  (lazy  ("    nonrec_complex_guard_hps: " ^ (!CP.print_svl nonrec_complex_guard_hps))) no_pos in
  let pre_preds_4_equal = List.fold_left (fun ls_cand (hp,cs,deps) ->
      if CP.intersect_svl deps nonrec_complex_guard_hps = [] then
        ls_cand@[(hp,cs)]
      else ls_cand
  ) [] pre_preds_cand_equal1 in
  (*mut rec dep*)
  let pre_preds_4_equal1 = (* if pre_preds_4_equal = [] && pre_preds_cand_equal1 <> [] then *)
    if  complex_nonrec_guard_grps = [] && pre_preds_4_equal <> [] then
      ranking_frozen_mutrec_preds pre_preds_cand_equal1
    else
      if complex_nonrec_guard_grps != [] then
        (*move guard with pure to the end*)
        (* let complex_nonrec_pguard_grps, rem = List.partition is_pure_guard complex_nonrec_guard_grps in *)
        (* (rem@complex_nonrec_pguard_grps) *)
        complex_nonrec_guard_grps
      else []
  in
  (*process_complex, nonrec, non depend on others
    testcases: check-dll.ss; check-sorted
  *)
  let pre_preds_4_equal2 = if pre_preds_4_equal1 = [] then
    (*remove the tupled ones*)
    let complex_nrec_ndep1 = List.filter (fun (hp,_) -> not(CP.mem_svl hp tupled_hps)) complex_nrec_ndep in
    match complex_nrec_ndep1 with
      | (hp,constrs)::_ ->  [(hp,constrs)]
      | _ -> []
  else pre_preds_4_equal1
  in
  let pre_preds_4_equal3 = if pre_preds_4_equal2 = [] then
    (*process_complex, nonrec*)
    match complex_nonrec_guard_grps with
      | (hp,constrs)::_ ->  [(hp,constrs)]
      | _ -> []
  else pre_preds_4_equal2
  in
  (*find rem_constrs for weaken*)
  let is_not_in_frozen complex_hps frozen_hps cs=
    let lhps = CF.get_hp_rel_name_formula cs.CF.hprel_lhs in
    if (CP.intersect_svl lhps frozen_hps) = [] || (CP.intersect_svl lhps complex_hps <> []) then true else false
  in
  let complex_hps1 = List.filter (fun hp -> not (CP.mem_svl hp tupled_hps)) complex_hps in
  let rem_constrs = if pre_preds_4_equal3 =[] then constrs else
    let hps = List.map fst pre_preds_4_equal3 in
    List.filter (is_not_in_frozen complex_hps hps) constrs
  in
  (pre_preds_4_equal3, complex_hps1,rem_constrs)

let icompute_action_pre constrs post_hps frozen_hps pre_fix_hps=
  let pr1 = pr_list_ln Cprinter.string_of_hprel_short in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv  pr1) in
  Debug.no_3 "icompute_action_pre" pr1 !CP.print_svl !CP.print_svl
      (pr_triple pr2 !CP.print_svl pr1)
      (fun _ _ _ -> icompute_action_pre_x constrs post_hps frozen_hps pre_fix_hps)
      constrs post_hps frozen_hps


let igen_action_pre equal_hps new_frozen_constrs =
  (*pick one for syn?*)
  (*do syn*)
  (*apply transitive*)
  I_pre_synz (equal_hps, new_frozen_constrs)

let icompute_action_pre_oblg ()=
  I_pre_oblg

let icompute_action_pre_fix pre_fix_hps=
  I_pre_fix pre_fix_hps

let icompute_action_post_fix post_fix_hps=
  I_post_fix post_fix_hps

let icompute_action_post ()=
  I_post_synz

let icompute_action_post_oblg ()=
  I_post_oblg
