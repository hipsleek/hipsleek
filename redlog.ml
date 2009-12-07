(*
 * Interact with reduce/redlog
 * Created on Aug 31, 2009
 *)

open Globals
module CP = Cpure

let is_log_all = ref false
let is_presburger = ref false
let is_ee = ref false
let integer_relax_mode = ref false
let is_hybrid = ref true
let is_reduce_running = ref false
let log_file = open_out ("allinput.rl")
let channels = ref (stdin, stdout)

(**********************
 * auxiliari function *
 **********************)

let log_all string = 
  if !is_log_all then begin
    output_string log_file (string ^ Util.new_line_str);
    flush log_file
  end

let send_cmd cmd =
  if !is_reduce_running then output_string (snd !channels) (cmd ^ "\n")

let rec remove_spaces s =
  if (String.length s > 0) then
    let rest = remove_spaces (String.sub s 1 ((String.length s) - 1)) in
    if (s.[0] = ' ') then rest
    else (String.make 1 s.[0]) ^ rest
  else s

(* start Reduce system in a separated process *)
let start_red () =
  if not !is_reduce_running then begin
    print_string "Starting Reduce/Redlog...\n";
    flush stdout;
    channels := Unix.open_process "redcsl -w 2>/dev/null";
    is_reduce_running := true;
    send_cmd "load_package redlog;";
    if !is_presburger then
      send_cmd "rlset pasf;"
    else
      send_cmd "rlset ofsf;";
    send_cmd "on rlnzden;";
    (* discard the version line *)
    let finished = ref false in
    while not !finished do
      let line = input_line (fst !channels) in
      if (String.length line > 6 && String.sub line 0 6 = "Reduce") then finished := true;
    done;
  end

(* stop Reduce system *)
let stop_red () = 
  if !is_reduce_running then begin
    send_cmd "quit;";
    flush (snd !channels);
    ignore (Unix.close_process !channels);
    is_reduce_running := false;
  end

(* send formula to reduce/redlog and receive result *)
let check_formula f =
  try
    output_string (snd !channels) f;
    flush (snd !channels);
    let result = ref false in
    let finished = ref false in
    while not !finished do
      let line = input_line (fst !channels) in
      if line = "true" then begin
        result := true;
        finished := true
      end else if line = "false" then begin
        result := false;
        finished := true
      end else if String.length line > 5 & (String.sub line 0 5) = "*****" then begin
        print_endline ("UNKNOWN Reduce output: " ^ line);
        result := false;
        finished := true
      end
    done;
    !result
  with _ -> 
    ignore (Unix.close_process !channels);
    is_reduce_running := false;
    print_endline "Reduce crashed or something really bad happenned! Restarting...";
    start_red ();
    false

let send_and_receive f =
  if !is_reduce_running then
    try
      output_string (snd !channels) f;
      flush (snd !channels);
      let result = ref "" in
      let finished = ref false in
      while not !finished do
        result := input_line (fst !channels);
        if (String.length !result > 5 && (String.sub !result 0 5) = "*****") || (String.length !result > 0 && (String.get !result 0) = '{') then
          finished := true
      done;
      !result
    with _ ->
      ignore (Unix.close_process !channels);
      is_reduce_running := false;
      print_endline "Reduce crashed or something really bad happenned! Restarting...";
      start_red ();
      ""
  else
    ""

let rec is_linear_exp exp = 
  match exp with
  | CP.Null _ | CP.Var _ | CP.IConst _ -> true
  | CP.Add (e1, e2, _) | CP.Subtract (e1, e2, _) -> (is_linear_exp e1) && (is_linear_exp e2)
  | CP.Mult (e1, e2, _) -> 
      let res = match e1 with
        | CP.IConst _ -> is_linear_exp e2
        | _ -> (match e2 with 
                 | CP.IConst _ -> is_linear_exp e1 
                 | _ -> false)
      in res
  | CP.Div (e1, e2, _) ->
      (match e2 with
        | CP.IConst _ -> is_linear_exp e1
        | _ -> false)
  | _ -> false

let is_linear_bformula b = 
  match b with
  | CP.BConst _ -> true
  | CP.BVar _ -> true
  | CP.Lt (e1, e2, _) | CP.Lte (e1, e2, _) 
  | CP.Gt (e1, e2, _) | CP.Gte (e1, e2, _)
  | CP.Eq (e1, e2, _) | CP.Neq (e1, e2, _)
      -> (is_linear_exp e1) & (is_linear_exp e2)
  | CP.EqMax (e1, e2, e3, _) | CP.EqMin (e1, e2, e3, _)
      -> (is_linear_exp e1) & (is_linear_exp e2) & (is_linear_exp e3)
  | _ -> false
  
let rec is_linear_formula f0 = 
  match f0 with
  | CP.BForm b -> is_linear_bformula b
  | CP.Not (f, _) | CP.Forall (_, f, _) | CP.Exists (_, f, _) -> is_linear_formula f;
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _) -> (is_linear_formula f1) & (is_linear_formula f2)

let rec has_existential_quantifier f0 negation_bounded =
  match f0 with 
  | CP.Exists (_, f, _) -> 
      if negation_bounded then 
        has_existential_quantifier f negation_bounded 
      else 
        true
  | CP.Forall (_, f, _) -> has_existential_quantifier f negation_bounded
  | CP.Not (f, _) -> has_existential_quantifier f (not negation_bounded)
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _) -> 
      (has_existential_quantifier f1 negation_bounded) ||
      (has_existential_quantifier f2 negation_bounded)
  | CP.BForm _ -> false

(**************************
 * cpure to reduce/redlog *
 **************************)

let rec rl_of_var_list (vars : ident list) : string =
  match vars with
  | [] -> ""
  | [v] -> v
  | v :: rest -> v ^ ", " ^ (rl_of_var_list rest)

let rl_of_spec_var (sv: CP.spec_var) = 
  match sv with
  | CP.SpecVar (_, v, _) -> v ^ (if CP.is_primed sv then Oclexer.primed_str else "")

let get_vars_formula (p : CP.formula) =
  let svars = Cpure.fv p in List.map rl_of_spec_var svars

let rec rl_of_exp e0 = 
  match e0 with
  | CP.Null _ -> "0" (* TEMP *)
  | CP.Var (v, _) -> rl_of_spec_var v
  | CP.IConst (i, _) -> string_of_int i
  | CP.FConst (f, _) -> string_of_float f
  | CP.Add (e1, e2, _) -> "(" ^ (rl_of_exp e1) ^ " + " ^ (rl_of_exp e2) ^ ")"
  | CP.Subtract (e1, e2, _) -> "(" ^ (rl_of_exp e1) ^ " - " ^ (rl_of_exp e2) ^ ")"
  | CP.Mult (e1, e2, _) -> "(" ^ (rl_of_exp e1) ^ " * " ^ (rl_of_exp e2) ^ ")"
  | CP.Div (e1, e2, _) -> "(" ^ (rl_of_exp e1) ^ " / " ^ (rl_of_exp e2) ^ ")"
  | CP.Max _
  | CP.Min _ -> failwith ("redlog.rl_of_exp: min/max can't appear here")
  | _ -> failwith ("redlog: bags is not supported")

let rl_of_b_formula b =
  let mk_bin_exp opt e1 e2 = 
    "(" ^ (rl_of_exp e1) ^ opt ^ (rl_of_exp e2) ^ ")"
  in 
  match b with
  | CP.BConst (c, _) -> if c then "true" else "false"
  | CP.BVar (bv, _) -> 
      (* To be honest, I don't know what I need to return in this case. *)
      (* So, the following solution is just a copy of what omega.ml used. *)
      "(" ^ (rl_of_spec_var bv) ^ " > 0)"
  | CP.Lt (e1, e2, l) -> mk_bin_exp " < " e1 e2
  | CP.Lte (e1, e2, l) -> mk_bin_exp " <= " e1 e2
  | CP.Gt (e1, e2, l) -> mk_bin_exp " > " e1 e2
  | CP.Gte (e1, e2, l) -> mk_bin_exp " >= " e1 e2
  | CP.Eq (e1, e2, _) -> mk_bin_exp " = " e1 e2
  | CP.Neq (e1, e2, _) -> mk_bin_exp " <> " e1 e2
  | CP.EqMax (e1, e2, e3, _) ->
      (* e1 = max(e2,e2) <-> ((e1 = e2 /\ e2 >= e3) \/ (e1 = e3 /\ e2 < e3)) *)
      let a1 = rl_of_exp e1 in
      let a2 = rl_of_exp e2 in
      let a3 = rl_of_exp e3 in
      "((" ^ a1 ^ " = " ^ a2 ^ " and " ^ a2 ^ " >= " ^ a3 ^ ") or ("
      ^ a1 ^ " = " ^ a3 ^ " and " ^ a2 ^ " <= " ^ a3 ^ "))"
  | CP.EqMin (e1, e2, e3, _) ->
      (* e1 = min(e2,e3) <-> ((e1 = e2 /\ e2 <= e3) \/ (e1 = e3 /\ e2 > e3)) *)
      let a1 = rl_of_exp e1 in
      let a2 = rl_of_exp e2 in
      let a3 = rl_of_exp e3 in
      "((" ^ a1 ^ " = " ^ a2 ^ " and " ^ a2 ^ " <= " ^ a3 ^ ") or ("
      ^ a1 ^ " = " ^ a3 ^ " and " ^ a2 ^ " >= " ^ a3 ^ "))"
  | _ -> failwith "redlog: bags is not supported"

let rec rl_of_formula f0 = 
  match f0 with
  | CP.BForm b -> rl_of_b_formula b 
  | CP.Not (f, _) -> "(not " ^ (rl_of_formula f) ^ ")"
  | CP.Forall (sv, f, _) -> "(all (" ^ (rl_of_spec_var sv) ^ ", " ^ (rl_of_formula f) ^ "))"
  | CP.Exists (sv, f, _) -> "(ex (" ^ (rl_of_spec_var sv) ^ ", " ^ (rl_of_formula f) ^ "))"
  | CP.And (f1, f2, _) -> "(" ^ (rl_of_formula f1) ^ " and " ^ (rl_of_formula f2) ^ ")"
  | CP.Or (f1, f2, _) -> "(" ^ (rl_of_formula f1) ^ " or " ^ (rl_of_formula f2) ^ ")"
  
let rec strengthen_formula f0 = 
  match f0 with
  | CP.BForm b -> 
      let r = match b with
        | CP.Lt (e1, e2, l) -> CP.BForm (CP.Lte (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l))
        | CP.Gt (e1, e2, l) -> CP.BForm (CP.Gte (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l))
        | _ -> f0 
      in r
  | CP.Not (f, l) -> CP.Not (strengthen_formula f, l)
  | CP.Forall (sv, f, l) -> CP.Forall (sv, strengthen_formula f, l)
  | CP.Exists (sv, f, l) -> CP.Exists (sv, strengthen_formula f, l)
  | CP.And (f1, f2, l) -> CP.And (strengthen_formula f1, strengthen_formula f2, l)
  | CP.Or (f1, f2, l) -> CP.Or (strengthen_formula f1, strengthen_formula f2, l)

let rec weaken_formula f0 = 
  match f0 with
  | CP.BForm b ->
      let r = match b with
        | CP.Lte (e1, e2, l) -> CP.BForm (CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l))
        | CP.Gte (e1, e2, l) -> CP.BForm (CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l))
        | CP.Eq (e1, e2, l) ->
            (* e1 = e2 => e2 - 1 < e1 < e2 + 1 *)
            let lp = CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l) in
            let rp = CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l) in
            CP.And (CP.BForm lp, CP.BForm rp, l)
        | _ -> f0 
      in r
  | CP.Not (f, l) -> CP.Not (weaken_formula f, l)
  | CP.Forall (sv, f, l) -> CP.Forall (sv, weaken_formula f, l)
  | CP.Exists (sv, f, l) -> CP.Exists (sv, weaken_formula f, l)
  | CP.And (f1, f2, l) -> CP.And (weaken_formula f1, weaken_formula f2, l)
  | CP.Or (f1, f2, l) -> CP.Or (weaken_formula f1, weaken_formula f2, l)
  
(***********************************
 existential quantifier elimination 
 **********************************)

let find_bound_b_formula v f0 =
  let parse s = 
    print_endline s;
    if s.[0] = '{' then
      let end_pos = String.index s ',' in
      let num = remove_spaces (String.sub s 1 (end_pos - 1)) in
      begin
      print_endline num;
      let res = float_of_string num in
      if (abs_float res) = infinity then
        None
      else
        Some res
      end
    else
      None
  in
  let ceil2 f =
    match f with
    | Some f0 -> Some (int_of_float (ceil f0))
    | None -> None
  in
  let floor2 f =
    match f with
    | Some f0 -> Some (int_of_float (floor (0. -. f0))) (* we find max by using redlog to find min of it neg val *)
    | None -> None
  in
  let find_min_cmd = "rlopt({" ^ (rl_of_b_formula f0) ^ "}, " ^ (rl_of_spec_var v) ^ ");\n" in
  let find_max_cmd = "rlopt({" ^ (rl_of_b_formula f0) ^ "}, -" ^ (rl_of_spec_var v) ^ ");\n" in
  send_cmd "on rounded;"; 
  let min_out = send_and_receive find_min_cmd in
  let max_out = send_and_receive find_max_cmd in
  send_cmd "off rounded;";
  let min = ceil2 (parse min_out) in
  let max = floor2 (parse max_out) in
  (min, max)

let rec elim_exists f0 = 
  match f0 with
  | CP.Exists (qvar, qf, pos) ->
      begin
        match qf with
        | CP.Or (qf1, qf2, qpos) ->
            let new_qf1 = CP.mkExists [qvar] qf1 qpos in
            let new_qf2 = CP.mkExists [qvar] qf2 qpos in
            let eqf1 = elim_exists new_qf1 in
            let eqf2 = elim_exists new_qf2 in
            let res = CP.mkOr eqf1 eqf2 pos in
            res
        | _ ->
            let eqqf = elim_exists qf in
            let min, max = find_bound qvar eqqf in
            begin
              match min, max with
              | Some mi, Some ma ->
                  begin
                  print_endline ("min = " ^ (string_of_int mi) ^ " & max = " ^ (string_of_int ma));
                  let res = ref (CP.mkFalse pos) in
                  begin
                    for i = mi to ma do
                      res := CP.mkOr !res (CP.apply_one_term (qvar, CP.IConst (i, no_pos)) eqqf) pos
                    done;
                    !res
                  end
                  end
              | _ -> f0
            end
      end
  | CP.And (f1, f2, pos) ->
      let ef1 = elim_exists f1 in
      let ef2 = elim_exists f2 in
      CP.mkAnd ef1 ef2 pos
  | CP.Or (f1, f2, pos) ->
      let ef1 = elim_exists f1 in
      let ef2 = elim_exists f2 in
      CP.mkOr ef1 ef2 pos
  | CP.Not (f1, pos) ->
      let ef1 = elim_exists f1 in
      CP.mkNot ef1 pos
  | CP.Forall (qvar, qf, pos) ->
      let eqf = elim_exists qf in
      CP.mkForall [qvar] eqf pos
  | CP.BForm _ -> f0

and find_bound v f0 =
  let f0 = strengthen_formula f0 in (* replace gt,lt with gte,lte to be able to find bound *)
  match f0 with
  | CP.And (f1, f2, _) ->
      begin
        let min1, max1 = find_bound v f1 in
        let min2, max2 = find_bound v f2 in
        let min = match min1, min2 with
          | None, None -> None
          | Some m1, Some m2 -> if m1 < m2 then min1 else min2
          | Some _, None -> min1
          | None, Some _ -> min2
        in
        let max = match max1, max2 with
          | None, None -> None
          | Some m1, Some m2 -> if m1 > m2 then max1 else max2
          | Some _, None -> max1
          | None, Some _ -> max2
        in
        (min, max)
      end
  | CP.BForm bf -> find_bound_b_formula v bf
  | _ -> None, None

(**********************
   Verification works  
 *********************)

let is_sat (f: CP.formula) (sat_no: string) : bool =
  log_all (Util.new_line_str ^ "#is_sat " ^ sat_no);
  log_all (Cprinter.string_of_pure_formula f);
  let frl = rl_of_formula f in
  let vars = get_vars_formula f in
  let vars_str = rl_of_var_list (Util.remove_dups vars) in
  let rl_input = "rlqe ex({" ^ vars_str ^ "}, " ^ frl ^ ");" in
  log_all ("[reduce/redlog] " ^ rl_input);
  (* let sat = run_reduce rl_input in *)
  let sat = check_formula (rl_input ^ "\n") in
  log_all (if sat then "FAIL" else "SUCCESS");
  sat

let imply (ante : CP.formula) (conseq: CP.formula) (imp_no: string) : bool =
  log_all (Util.new_line_str ^ "#imply " ^ imp_no);
  log_all ("ante: " ^ (Cprinter.string_of_pure_formula ante));
  log_all ("conseq: " ^ (Cprinter.string_of_pure_formula conseq));
  (* TODO: only weakening and strengthening the formula if it's an integer
   * formula *)
  let ante = if !is_ee then elim_exists ante else ante in
  let conseq = if !is_ee then elim_exists conseq else conseq in
  let _ = if (has_existential_quantifier ante true) || (has_existential_quantifier conseq false) then 
    log_all "## Warning: Found formula with existential quantified var(s), result may be unsound!" in
  let s_ante = if !integer_relax_mode then strengthen_formula ante else ante in
  let w_conseq = if !integer_relax_mode then weaken_formula conseq else conseq in
  let rl_of_ante = rl_of_formula s_ante in
  let rl_of_conseq = rl_of_formula w_conseq in
  if (rl_of_ante = "false" || rl_of_conseq = "true") then begin
    log_all ("obvious case: SUCCESS.");
    true
  end else begin
    let frl = 
      if rl_of_ante = "true" then rl_of_conseq
      else rl_of_ante ^ " impl " ^ rl_of_conseq 
    in
    let vars_ante = get_vars_formula ante in
    let vars_conseq = get_vars_formula conseq in
    let vars = List.append vars_ante vars_conseq in
    let vars_str = rl_of_var_list (Util.remove_dups vars) in
    let rl_input = "rlqe all({" ^ vars_str ^ "}, " ^ frl ^ ");" in
    log_all ("[reduce/redlog] " ^ rl_input);
    (* let sat = run_reduce rl_input in *)
    let sat = check_formula (rl_input ^ "\n") in
    log_all (if sat then "SUCCESS" else "FAIL");
    sat
  end

(* just prototype *)
let simplify (f: CP.formula) : CP.formula =
    (*
    let frl = rl_of_formula f in
    log_all (Util.new_line_str ^ "#simplify (currently doesn't do anything)");
    log_all frl;
    *)
    f
 
let hull (f: CP.formula) : CP.formula = 
    (*
    let frl = rl_of_formula f in
    log_all (Util.new_line_str ^ "#hull");
    log_all frl;
    *)
    f

let pairwisecheck (f: CP.formula): CP.formula =
    (*
    let frl = rl_of_formula f in
    log_all (Util.new_line_str ^ "#pairwisecheck");
    log_all frl;
    *)
    f

