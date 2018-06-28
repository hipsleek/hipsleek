open SBLib
open SBLib.Basic
open SBCast
open SBGlobals
open SBProof
open Printf

module PS = SBProcess

type rule_id = int

type goal_profile = {
  gpf_lratio_datas : ratio;
  gpf_lratio_views : ratio;
  gpf_lratio_data_same_root : ratio;
  gpf_lratio_data_common_vars : ratio;
  gpf_lratio_view_common_vars : ratio;
  gpf_lratio_view_common_roots : ratio;
  gpf_lratio_heap_common_vars : ratio;
  gpf_lratio_views_hdrec : ratio;
  gpf_lratio_views_tlrec : ratio;
  gpf_lratio_views_mdrec : ratio;
  gpf_lratio_views_mxrec : ratio;
  gpf_rratio_datas : ratio;
  gpf_rratio_views : ratio;
  gpf_rratio_data_same_root : ratio;
  gpf_rratio_data_common_vars : ratio;
  gpf_rratio_view_common_vars : ratio;
  gpf_rratio_view_common_roots : ratio;
  gpf_rratio_heap_common_vars : ratio;
  gpf_rratio_views_hdrec : ratio;
  gpf_rratio_views_tlrec : ratio;
  gpf_rratio_views_mdrec : ratio;
  gpf_rratio_views_mxrec : ratio;
  gpf_rratio_qvars_datas : ratio;
  gpf_rratio_qvars_views : ratio;
  gpf_gratio_data_same_root : ratio;
  gpf_gratio_data_common_vars : ratio;
  gpf_gratio_view_common_vars : ratio;
  gpf_gratio_view_common_roots : ratio;
  gpf_gratio_heap_common_vars : ratio;
  gpf_tratio_induction : ratio;
  gpf_tratio_hypothesis : ratio;
  gpf_tratio_view_right : ratio;
  gpf_tratio_star_data : ratio;
  gpf_tratio_star_view : ratio;
}

(* TODO: trace rules *)

type rule_profile = {
  rpf_mrule : meta_rule;
  rpf_hpos_left : heap_pos;
  rpf_hpos_right : heap_pos;
}

let fname_query_rule = "query_rule.xml"

let fname_query_pred = "query_pred.xml"

let proc =
  let args = [|"python"; "QueryRule.py"; "-i"; "-t"; "3"|] in
  ref (PS.mk_dummy_proc "ML" "python" args)

let mrule_invalid = MrUnknown

let mrule_id_invalid = -1

let meta_rule_ids =
  [ (MrStarData, 0);
    (MrStarView, 1);
    (MrViewRight, 2);
    (MrInduction, 3);
    (MrHypothesis, 4);
    (MrTheorem, 5);
    (MrExclMid, 6);
    (MrUnknown, -1) ]

let is_valid_meta_rule rule =
  let mrule = get_meta_rule rule in
  match mrule with
  | MrUnknown -> false
  | _ -> true

let get_mrule_id mrule : int =
  try snd (meta_rule_ids |> List.find (fst >> (=) mrule))
  with _ -> mrule_id_invalid

let get_rule_id rule : int =
  let mrule = get_meta_rule rule in
  get_mrule_id mrule

let get_mrule_from_id id : meta_rule =
  try fst (meta_rule_ids |> List.find (snd >> (=) id))
  with _ -> mrule_invalid

let encode_heap_pos hpos = match hpos with
  | HpHead -> 1
  | HpTail -> 2
  | HpHdtl -> 3
  | HpUnkn -> 0

let decode_heap_pos hpos = match hpos with
  | 1 -> HpHead
  | 2 -> HpTail
  | 3 -> HpHdtl
  | _ -> HpUnkn

let mk_goal_profile prog goal =
  let vdefns = prog.prog_views in
  let lst, rst = goal.gl_lstats, goal.gl_rstats in
  let num_lds, num_rds = lst.fst_num_datas, rst.fst_num_datas in
  let num_lvs, num_rvs = lst.fst_num_views, rst.fst_num_views in
  let num_lhas, num_rhas = lst.fst_num_hatoms, rst.fst_num_hatoms in
  let num_ds = lst.fst_num_datas + rst.fst_num_datas in
  let num_vs = lst.fst_num_views + rst.fst_num_views in
  let num_has = lst.fst_num_hatoms + rst.fst_num_hatoms in
  let num_lvs_hdrec, num_lvs_tlrec, num_lvs_mdrec, num_lvs_mxrec =
    let hd, tl, md, mx = ref 0, ref 0, ref 0, ref 0 in
    let _ = lst.fst_views |> List.iter (fun vf ->
      let recur_direct = get_view_recur_direction vdefns vf in
      match recur_direct with
      | VrdHead -> hd := !hd + 1
      | VrdTail -> tl := !tl + 1
      | VrdMid -> md := !md + 1
      | VrdMix -> mx := !mx + 1
      | _ -> ()) in
    (!hd, !tl, !md, !mx) in
  let num_rvs_hdrec, num_rvs_tlrec, num_rvs_mdrec, num_rvs_mxrec =
    let hd, tl, md, mx = ref 0, ref 0, ref 0, ref 0 in
    let _ = rst.fst_views |> List.iter (fun vf ->
      let recur_direct = get_view_recur_direction vdefns vf in
      match recur_direct with
      | VrdHead -> hd := !hd + 1
      | VrdTail -> tl := !tl + 1
      | VrdMid -> md := !md + 1
      | VrdMix -> mx := !mx + 1
      | _ -> ()) in
    (!hd, !tl, !md, !mx) in
  let num_lhatoms, num_rhatoms = lst.fst_num_hatoms, rst.fst_num_hatoms in
  let num_ldata_sroot = lst.fst_datas |> List.filter (fun hd ->
    List.exists (is_same_root_df hd) rst.fst_datas) |> List.length in
  let num_ldata_cvar = lst.fst_datas |> List.filter (fun hd ->
    List.exists (is_common_args_df hd) rst.fst_datas) |> List.length in
  let num_rdata_sroot = rst.fst_datas |> List.filter (fun hd ->
    List.exists (is_same_root_df hd) lst.fst_datas) |> List.length in
  let num_rdata_cvar = rst.fst_datas |> List.filter (fun hd ->
    List.exists (is_common_args_df hd) lst.fst_datas) |> List.length in
  let num_data_sroot = num_ldata_sroot + num_rdata_sroot in
  let num_data_cvar = num_ldata_cvar + num_rdata_cvar in
  let num_lview_cvar = lst.fst_views |> List.filter (fun hv ->
    List.exists (is_common_args_vf hv) rst.fst_views) |> List.length in
  let num_lview_croot = lst.fst_views |> List.filter (fun hv1 ->
    List.exists (fun hv2 ->
      let roots1 = get_view_root vdefns hv1 in
      let roots2 = get_view_root vdefns hv2 in
      List.exists_pair eq_exp roots1 roots2) rst.fst_views) |> List.length in
  let num_rview_cvar = rst.fst_views |> List.filter (fun hv ->
    List.exists (is_common_args_vf hv) lst.fst_views) |> List.length in
  let num_rview_croot = rst.fst_views |> List.filter (fun hv1 ->
    List.exists (fun hv2 ->
      let roots1 = get_view_root vdefns hv1 in
      let roots2 = get_view_root vdefns hv2 in
      List.exists_pair eq_exp roots1 roots2) lst.fst_views) |> List.length in
  let num_view_cvar = num_lview_cvar + num_rview_cvar in
  let num_view_croot = num_lview_croot + num_rview_croot in
  let num_lheap_cvar = lst.fst_hatoms |> List.filter (fun ha ->
    intersected_vs (fv_ha ha) rst.fst_fvs) |> List.length in
  let num_rheap_cvar = rst.fst_hatoms |> List.filter (fun ha ->
    intersected_vs (fv_ha ha) lst.fst_fvs) |> List.length in
  let num_heap_cvar = num_lheap_cvar + num_rheap_cvar in
  let num_rqvars_datas = rst.fst_qvs |> List.filter (fun v ->
    rst.fst_datas |> List.exists (fv_df >> (mem_vs v))) |> List.length in
  let num_rqvars_views = rst.fst_qvs |> List.filter (fun v ->
    rst.fst_views|> List.exists (fv_vf >> (mem_vs v))) |> List.length in
  let num_rqvars = List.length rst.fst_qvs in
  let num_latest_rules = 5 in
  let latest_srules =
    let srules = collect_used_spatial_rules goal in
    if List.length srules < num_latest_rules then srules
    else srules |> List.split_nth num_latest_rules |> fst in
  let num_rhypo, num_rindt, num_rvleft = ref 0, ref 0, ref 0 in
  let num_rvright, num_rsdata, num_rsview = ref 0, ref 0, ref 0 in
  let _ = latest_srules |> List.iter (function
    | RlHypothesis _ -> num_rhypo := !num_rhypo + 1
    | RlInduction _ -> num_rindt := !num_rindt + 1
    | RlViewRight _ -> num_rvright := !num_rvright + 1
    | RlStarData _ -> num_rsdata := !num_rsdata + 1
    | RlStarView _ -> num_rsview := !num_rsview + 1
    | _ -> ()) in
  { gpf_lratio_datas = mk_ratio num_lds num_lhatoms;
    gpf_lratio_views = mk_ratio num_lvs num_lhatoms;
    gpf_lratio_data_same_root = mk_ratio num_ldata_sroot num_lds;
    gpf_lratio_data_common_vars = mk_ratio num_ldata_cvar num_lds;
    gpf_lratio_view_common_vars = mk_ratio num_lview_cvar num_lvs;
    gpf_lratio_view_common_roots = mk_ratio num_lview_croot num_lvs;
    gpf_lratio_heap_common_vars = mk_ratio num_lheap_cvar num_lhas;
    gpf_lratio_views_hdrec = mk_ratio num_lvs_hdrec num_lhatoms;
    gpf_lratio_views_tlrec = mk_ratio num_lvs_tlrec num_lhatoms;
    gpf_lratio_views_mdrec = mk_ratio num_lvs_mdrec num_lhatoms;
    gpf_lratio_views_mxrec = mk_ratio num_lvs_mxrec num_lhatoms;
    gpf_rratio_datas = mk_ratio num_rds num_rhatoms;
    gpf_rratio_views = mk_ratio num_rvs num_rhatoms;
    gpf_rratio_data_same_root = mk_ratio num_rdata_sroot num_rds;
    gpf_rratio_data_common_vars = mk_ratio num_rdata_cvar num_rds;
    gpf_rratio_view_common_vars = mk_ratio num_rview_cvar num_rvs;
    gpf_rratio_view_common_roots = mk_ratio num_rview_croot num_lvs;
    gpf_rratio_heap_common_vars = mk_ratio num_rheap_cvar num_rhas;
    gpf_rratio_views_hdrec = mk_ratio num_rvs_hdrec num_rhatoms;
    gpf_rratio_views_tlrec = mk_ratio num_rvs_tlrec num_rhatoms;
    gpf_rratio_views_mdrec = mk_ratio num_rvs_mdrec num_rhatoms;
    gpf_rratio_views_mxrec = mk_ratio num_rvs_mxrec num_rhatoms;
    gpf_rratio_qvars_datas = mk_ratio num_rqvars_datas num_rqvars;
    gpf_rratio_qvars_views = mk_ratio num_rqvars_views num_rqvars;
    gpf_gratio_data_same_root = mk_ratio num_data_sroot num_ds;
    gpf_gratio_data_common_vars = mk_ratio num_data_cvar num_ds;
    gpf_gratio_view_common_vars = mk_ratio num_view_cvar num_vs;
    gpf_gratio_view_common_roots = mk_ratio num_view_croot num_vs;
    gpf_gratio_heap_common_vars = mk_ratio num_heap_cvar num_has;
    gpf_tratio_hypothesis = mk_ratio !num_rhypo num_latest_rules;
    gpf_tratio_induction = mk_ratio !num_rindt num_latest_rules;
    gpf_tratio_view_right = mk_ratio !num_rvright num_latest_rules;
    gpf_tratio_star_data = mk_ratio !num_rsdata num_latest_rules;
    gpf_tratio_star_view = mk_ratio !num_rsview num_latest_rules; }

let dump_goal_profile prog goal =
  let gp = mk_goal_profile prog goal in
  let gp_data = [
    ("lratio_datas", MvRatio gp.gpf_lratio_datas);
    ("lratio_views", MvRatio gp.gpf_lratio_views);
    ("lratio_data_same_root", MvRatio gp.gpf_lratio_data_same_root);
    ("lratio_data_common_var", MvRatio gp.gpf_lratio_data_common_vars);
    ("lratio_view_common_var", MvRatio gp.gpf_lratio_view_common_vars);
    ("lratio_view_common_roots", MvRatio gp.gpf_lratio_view_common_roots);
    ("lratio_heap_common_var", MvRatio gp.gpf_lratio_heap_common_vars);
    ("lratio_views_hdrec", MvRatio gp.gpf_lratio_views_hdrec);
    ("lratio_views_tlrec", MvRatio gp.gpf_lratio_views_tlrec);
    ("lratio_views_mxrec", MvRatio gp.gpf_lratio_views_mxrec);
    ("rratio_datas", MvRatio gp.gpf_rratio_datas);
    ("rratio_views", MvRatio gp.gpf_rratio_views);
    ("rratio_data_same_root", MvRatio gp.gpf_rratio_data_same_root);
    ("rratio_data_common_var", MvRatio gp.gpf_rratio_data_common_vars);
    ("rratio_view_common_var", MvRatio gp.gpf_rratio_view_common_vars);
    ("rratio_view_common_roots", MvRatio gp.gpf_rratio_view_common_roots);
    ("rratio_heap_common_var", MvRatio gp.gpf_rratio_heap_common_vars);
    ("rratio_views_hdrec", MvRatio gp.gpf_rratio_views_hdrec);
    ("rratio_views_tlrec", MvRatio gp.gpf_rratio_views_tlrec);
    ("rratio_views_mxrec", MvRatio gp.gpf_rratio_views_mxrec);
    ("rratio_qvars_datas", MvRatio gp.gpf_rratio_qvars_datas);
    ("rratio_qvars_views", MvRatio gp.gpf_rratio_qvars_views);
    ("gratio_data_same_root", MvRatio gp.gpf_gratio_data_same_root);
    ("gratio_data_common_var", MvRatio gp.gpf_gratio_data_common_vars);
    ("gratio_view_common_var", MvRatio gp.gpf_gratio_view_common_vars);
    ("gratio_view_common_roots", MvRatio gp.gpf_gratio_view_common_roots);
    ("gratio_heap_common_var", MvRatio gp.gpf_gratio_heap_common_vars);
    ("tratio_hypothesis", MvRatio gp.gpf_tratio_hypothesis);
    ("tratio_induction", MvRatio gp.gpf_tratio_induction);
    ("tratio_view_right", MvRatio gp.gpf_tratio_view_right);
    ("tratio_star_data", MvRatio gp.gpf_tratio_star_data);
    ("tratio_star_view", MvRatio gp.gpf_tratio_star_view); ] in
  let gp_data =
    gp_data |> List.map (fun (tag, v) ->
      "  <" ^ tag ^ "> " ^ (pr_mvalue v) ^ " </" ^ tag ^ ">") |>
    String.concat "\n" in
  "<profile>\n"^ gp_data ^ "\n" ^ "</profile>"

let mk_rule_profile prog goal rule =
  let mrule = get_meta_rule rule in
  let lst, rst = goal.gl_lstats, goal.gl_rstats in
  let hpos_left =
    let lhatom = match rule with
      | RlStarData {rsd_lg_data = ldata} -> Some (HData ldata)
      | RlStarView {rsv_lg_view = lview} -> Some (HView lview)
      | RlInduction {rid_lg_view = lview} -> Some (HView lview)
      | _ -> None in
    match lhatom with
    | None -> HpUnkn
    | Some ha ->
      if List.exists (eq_hatom ha) lst.fst_hatom_heads then HpHead
      else if List.exists (eq_hatom ha) lst.fst_hatom_tails then HpTail
      else if List.exists (eq_hatom ha) lst.fst_hatom_hdtls then HpHdtl
      else HpUnkn in
  let hpos_right =
    let lhatom = match rule with
      | RlStarData {rsd_rg_data = rdata} -> Some (HData rdata)
      | RlStarView {rsv_rg_view = rview} -> Some (HView rview)
      | RlViewRight {rvr_rg_view = rview} -> Some (HView rview)
      | _ -> None in
    match lhatom with
    | None -> HpUnkn
    | Some ha ->
      if List.exists (eq_hatom ha) rst.fst_hatom_heads then HpHead
      else if List.exists (eq_hatom ha) rst.fst_hatom_tails then HpTail
      else if List.exists (eq_hatom ha) rst.fst_hatom_hdtls then HpHdtl
      else HpUnkn in
  { rpf_mrule = mrule;
    rpf_hpos_left = hpos_left;
    rpf_hpos_right = hpos_right; }

let dump_rule_profile prog goal rule =
  let rp = mk_rule_profile prog goal rule in
  let rp_data = [
    ("rule_id", get_mrule_id rp.rpf_mrule);
    ("heap_left", encode_heap_pos rp.rpf_hpos_left);
    ("heap_right", encode_heap_pos rp.rpf_hpos_right)] in
  let rp_data = rp_data |>
                List.map (fun (tag, v) ->
                  "  <" ^ tag ^ "> " ^ (pr_int v) ^ " </" ^ tag ^ ">") |>
                String.concat "\n" in
  "<rprofile>\n"^ rp_data ^ "\n" ^ "</rprofile>"

let start_server () =
  DB.nhprint "QueryRule Old PID: " string_of_int !proc.PS.prc_pid;
  if !proc.PS.prc_pid = PS.pid_invalid then
    if not (PS.check_proc_alive !proc) then   (* this is very slow *)
      let prover = !proc.PS.prc_name in
      let cmd = !proc.PS.prc_cmd in
      let args = ["python"; "QueryRule.py"; "-i"] in
      let args = match (eq_s !machine_learning_enginee "") with
        | true -> args
        | false -> args @ ["-m"; !machine_learning_enginee] in
      let args = match !proof_interactive with
        | false -> args @ ["-t"; "5"]  (* timeout when in batch mode *)
        | true -> args in
      let args = Array.of_list args in
      proc := PS.start_process prover cmd args;
    else ();
  DB.nhprint "QueryRule New PID: " string_of_int !proc.PS.prc_pid

let stop_prover () =
  let () = PS.stop_process !proc in
  proc := {!proc with PS.prc_pid = PS.pid_invalid}

let send_input proc input =
  DB.nhprint "ML: query input: " pr_id input;
  let input = input ^ "\n" in
  output_string proc.PS.prc_out_channel input;
  flush proc.PS.prc_out_channel

let extract_string str prefix suffix =
  let start = (Str.search_forward (Str.regexp prefix) str 0)
              + (String.length prefix) in
  let len = (Str.search_backward (Str.regexp suffix)
               str (String.length str - 1)) - start  in
  let data = String.sub str start len in
  String.trim data

let read_output_rule proc : (meta_rule * float) list =
  let prefix, suffix = "Output rule: (", ")" in
  let rec read proc acc =
    try
      DB.nhprint "Read output: PID: " pr_int proc.PS.prc_pid;
      let line = String.trim (input_line proc.PS.prc_in_channel) in
      DB.nhprint "One line output: " pr_id line;
      if (String.exists line prefix) then line
      else read proc ""
    with | End_of_file -> acc in
  let output = read proc "" in
  DB.dhprint "ML query rule: output: " pr_id output;
  let rpredict = extract_string output prefix suffix in
  DB.dhprint "ML: rule prediction: " pr_id rpredict;
  try
    rpredict |> Str.split (Str.regexp ";") |>
    List.map (fun rp ->
      let rule_info = extract_string rp "(" ")" |>
                      Str.split (Str.regexp ",") in
      let rule_id, rule_confidence = match rule_info with
        | x::y::[] -> (int_of_string x, float_of_string y)
        | _ -> error "read_output_rule: expect rule id & confidence" in
      let mr = get_mrule_from_id rule_id in
      (mr, rule_confidence))
  with _ ->
    herror "mlearn: read_output: invalid rule prediction: " pr_id rpredict

let query_rule prog goal : (meta_rule * float) list =
  try
    let _ = start_server () in
    DB.dhprint "ML query rule: Current Goal: " pr_g goal;
    (* DB.dhprint "ML: All Possible Rules: " pr_rules rules; *)
    let input =
      let gp_data = dump_goal_profile prog goal in
      let extra_info =
        "<!-- Ent: \n  " ^ (pr_gent goal) ^ " -->\n" ^
        "<!-- Trace: " ^
        (goal.gl_trace |> List.rev |>
         pr_list_sbrace ~sep:"\n  ==> " pr_tri) ^
        " -->\n" in
      if !machine_learning_send_filename then
        let data =
          "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\n" ^
          "<goal>\n" ^
          extra_info ^ "\n" ^
          gp_data ^ "\n" ^
          "</goal>" in
        let file = open_out fname_query_rule in
        let _ = fprintf file "%s\n" data in
        let _ = close_out file in
        (Sys.getcwd ()) ^ "/" ^ fname_query_rule
      else gp_data in
    let _ = send_input !proc input in
    let rpredict = read_output_rule !proc in
    let rpredict =
      if List.length rpredict < !machine_learning_top_rules then rpredict
      else rpredict |> List.split_nth !machine_learning_top_rules |> fst in
    let rinfo = rpredict |> List.map (fun (mr, cfd) ->
      "(Rule: " ^ (pr_mrule mr) ^ ", ID: " ^ (pr_int (get_mrule_id mr))
      ^ ", confidence: " ^ (pr_float cfd) ^ ")") |> String.concat "; " in
    DB.rhprint ">>> ML recommend meta-rule: " pr_id rinfo;
    rpredict
  with e -> herror"ML query rule: exception" Printexc.to_string e

let read_output_heap_pos proc : (int * int) =
  let prefix, suffix = "Output pred: (", ")" in
  let rec read proc acc =
    try
      DB.nhprint "Read output: PID: " pr_int proc.PS.prc_pid;
      let line = String.trim (input_line proc.PS.prc_in_channel) in
      DB.nhprint "One line output: " pr_id line;
      if (String.exists line prefix) then line
      else read proc ""
    with End_of_file -> acc in
  let output = read proc "" in
  DB.dhprint "ML query pred: output: " pr_id output;
  try
    let poses = extract_string output prefix suffix |>
                Str.split (Str.regexp " ") |> List.map int_of_string in
    DB.nhprint "ML: POS: " pr_id poses;
    match poses with
    | x::y::[] -> (x, y)
    | _ -> error "read_output_heap_pos: expect left & right postition"
  with _ -> herror "mlearn: read_output: invalid pred pos: " pr_id output

let query_heap_pos prog goal mrule : heap_pos * heap_pos =
  try
    let _ = start_server () in
    DB.dhprint "ML query pred: Current Goal: " pr_g goal;
    (* DB.dhprint "ML: All Possible Rules: " pr_rules rules; *)
    let input =
      let gp_data = dump_goal_profile prog goal in
      let rid = mrule |> get_mrule_id |> string_of_int in
      if !machine_learning_send_filename then
        let data =
          "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\n"
          ^ "<goal>\n"
          ^ gp_data ^ "\n"
          ^ "<rule_id> " ^ rid ^ "</rule_id>\n"
          ^ "</goal>" in
        let file = open_out fname_query_pred in
        let _ = fprintf file "%s\n" data in
        let _ = close_out file in
        (Sys.getcwd ()) ^ "/" ^ fname_query_pred
      else gp_data in
    DB.dhprint "ML query pred: input: " pr_id input;
    let _ = send_input !proc input in
    let x, y = read_output_heap_pos !proc in
    let lpos, rpos = decode_heap_pos x, decode_heap_pos y in
    let pinfor = (pr_hpos lpos) ^ " -- " ^ (pr_hpos rpos) in
    let lst, rst = goal.gl_lstats, goal.gl_rstats in
    DB.nhprint "Entailment: " pr_gent goal;
    DB.nhprint "   lhs heads: " pr_has lst.fst_hatom_heads;
    DB.nhprint "   lhs tails: " pr_has lst.fst_hatom_tails;
    DB.nhprint "   lhs hdtls: " pr_has lst.fst_hatom_hdtls;
    DB.nhprint "   rhs heads: " pr_has rst.fst_hatom_heads;
    DB.nhprint "   rhs tails: " pr_has rst.fst_hatom_tails;
    DB.nhprint "   rhs hdtls: " pr_has rst.fst_hatom_hdtls;
    DB.rhprint ">>> ML recommend predicate pos: " pr_id pinfor;
    (lpos, rpos)
  with e -> herror"ML query pred: exception" Printexc.to_string e
