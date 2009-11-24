(*
 * Interact with reduce/redlog
 * Created on Aug 31, 2009
 *)

open Globals
module CP = Cpure

let is_log_all = ref false
let is_presburger = ref false
let integer_mode = ref false
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
let rec check_formula f =
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

let rec is_linear_exp exp =
  match exp with
  | CP.Null _ | CP.Var _ | CP.IConst _ -> true
  | CP.Add (e1, e2, _) | CP.Subtract (e1, e2, _) -> (is_linear_exp e1) & (is_linear_exp e2)
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
  
let rec is_linear_formula f0 = match f0 with
  | CP.BForm b -> is_linear_bformula b
  | CP.Not (f, _) | CP.Forall (_, f, _) | CP.Exists (_, f, _) -> is_linear_formula f;
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _) -> (is_linear_formula f1) & (is_linear_formula f2)

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
  | CP.Exists (sv, f, _) -> 
      (log_all "##Caution: existential formula found, result may be unsound.";
       log_all (Cprinter.string_of_pure_formula f0);
      "(ex (" ^ (rl_of_spec_var sv) ^ ", " ^ (rl_of_formula f) ^ "))")
  | CP.And (f1, f2, _) -> "(" ^ (rl_of_formula f1) ^ " and " ^ (rl_of_formula f2) ^ ")"
  | CP.Or (f1, f2, _) -> "(" ^ (rl_of_formula f1) ^ " or " ^ (rl_of_formula f2) ^ ")"
  
let rec strengthen_formula f0 =
  match f0 with
  | CP.BForm b -> 
      let r = match b with
        | CP.Lt (e1, e2, l) -> CP.BForm (CP.Lte (e1, CP.Add(e2, CP.IConst (-1, l), l), l))
        | CP.Gt (e1, e2, l) -> CP.BForm (CP.Gte (e1, CP.Add(e2, CP.IConst (1, l), l), l))
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
        | CP.Lte (e1, e2, l) -> CP.BForm (CP.Lt (e1, CP.Add(e2, CP.IConst (1, l), l), l))
        | CP.Gte (e1, e2, l) -> CP.BForm (CP.Gt (e1, CP.Add(e2, CP.IConst (-1, l), l), l))
        | CP.Eq (e1, e2, l) ->
            (* e1 = e2 => e2 - 1 < e1 < e2 + 1 *)
            let lp = CP.Gt (e1, CP.Add(e2, CP.IConst (-1, l), l), l) in
            let rp = CP.Lt (e1, CP.Add(e2, CP.IConst (1, l), l), l) in
            CP.And (CP.BForm lp, CP.BForm rp, l)
        | _ -> f0 
      in r
  | CP.Not (f, l) -> CP.Not (weaken_formula f, l)
  | CP.Forall (sv, f, l) -> CP.Forall (sv, weaken_formula f, l)
  | CP.Exists (sv, f, l) -> CP.Exists (sv, weaken_formula f, l)
  | CP.And (f1, f2, l) -> CP.And (weaken_formula f1, weaken_formula f2, l)
  | CP.Or (f1, f2, l) -> CP.Or (weaken_formula f1, weaken_formula f2, l)

(**********************
 * Verification works *
 **********************)

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
  let s_ante = if !integer_mode then strengthen_formula ante else ante in
  let w_conseq = if !integer_mode then weaken_formula conseq else conseq in
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
    let frl = rl_of_formula f in
    log_all (Util.new_line_str ^ "#simplify (currently doesn't do anything)");
    log_all frl;
    f
 
let hull (f: CP.formula) : CP.formula = 
    let frl = rl_of_formula f in
    log_all (Util.new_line_str ^ "#hull");
    log_all frl;
    f

let pairwisecheck (f: CP.formula): CP.formula =
    let frl = rl_of_formula f in
    log_all (Util.new_line_str ^ "#pairwisecheck");
    log_all frl;
    f

