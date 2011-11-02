(*
 * Interact with reduce/redlog
 * Created on Aug 31, 2009
 *)

open Globals
module CP = Cpure

(* options *)
let is_presburger = ref false
let no_pseudo_ops = ref false
let no_elim_exists = ref false
let no_simplify = ref false
let no_cache = ref false
let timeout = ref 10.0 (* default timeout is 15 seconds *)

(* logging *)
let is_log_all = ref false
let log_file = open_out "allinput.rl"

(* process management *)
let is_reduce_running = ref false

(* cache *)
let sat_cache = ref (Hashtbl.create 100)
let impl_cache = ref (Hashtbl.create 100)
(* threshold for caching *)
let cache_threshold = 0.001 (* 1ms *)

(* data collecting stuffs *)
let omega_call_count = ref 0
let redlog_call_count = ref 0
let ee_call_count = ref 0
let success_ee_count = ref 0
let nonlinear_time = ref 0.0
let linear_time = ref 0.0
let cached_count = ref 0

let prompt_regexp = Str.regexp "^[0-9]+:$"

let process = ref {name = "mona"; pid = 0;  inchannel = stdin; outchannel = stdout; errchannel = stdin}

(**********************
 * auxiliari function *
 **********************)

let start_with str prefix =
  (String.length str >= String.length prefix) && (String.sub str 0 (String.length prefix) = prefix) 

(* helper for logging *)
type log_level =
  | ERROR
  | DEBUG

let log level msg = 
  let write_msg () = output_string log_file (msg ^ "\n") in
  match level with
    | ERROR -> write_msg ()
    | DEBUG -> if !is_log_all then write_msg ()

(*
 * read from input channel until we found the reduce's prompt
 * return every lines read
 *)
let rec read_till_prompt (channel: in_channel) : string = 
  let line = Gen.trim_str (input_line channel) in
  let match_prompt = Str.string_match prompt_regexp line 0 in
  if match_prompt then ""
  else line ^ (read_till_prompt channel)

(* 
 * send cmd to reduce
 * for some weird i/o reasons, the reduce's prompt for this cmd
 * can only be read after we send this cmd, thus after send the cmd
 * to reduce, we read till the prompt (of this cmd) is found to discard it
 *)
let send_cmd cmd =
  if !is_reduce_running then 
    let cmd = cmd ^ ";\n" in
    let _ = output_string !process.outchannel cmd in
    let _ = flush !process.outchannel in
    let _ = read_till_prompt !process.inchannel in
    ()

(* start Reduce system in a separated process and load redlog package *)
let start () =
  if not !is_reduce_running then begin
      let prelude () =    
        is_reduce_running := true;
        send_cmd "off nat";
        send_cmd "linelength 10000";
        send_cmd "load_package redlog";
        send_cmd "rlset ofsf";
        send_cmd "on rlnzden";
      in
      let set_process proc = process := proc in
      let _ = Procutils.PrvComms.start !is_log_all log_file ("redlog", "redcsl",  [|"-w"; "-b";"-l reduce.log"|] ) set_process prelude in
      print_endline "Starting Reduce... "; flush stdout
  end

(* stop Reduce system *)
let stop () = 
  if !is_reduce_running then begin
      let ending_fnc () = 
        let outchannel = !process.outchannel in
        output_string outchannel "quit;\n"; flush outchannel;
        print_endline "Halting Reduce... "; flush stdout;
        log DEBUG "\n***************";
        log DEBUG ("Number of Omega calls: " ^ (string_of_int !omega_call_count));
        log DEBUG ("Number of Redlog calls: " ^ (string_of_int !redlog_call_count));
        log DEBUG ("Number of formulas that need ee: " ^ (string_of_int !ee_call_count));
        log DEBUG ("Number of successful ee calls: " ^ (string_of_int !success_ee_count));
        log DEBUG ("Number of cached hit: " ^ (string_of_int !cached_count));
        log DEBUG ("Nonlinear verification time: " ^ (string_of_float !nonlinear_time));
        log DEBUG ("Linear verification time: " ^ (string_of_float !linear_time))
      in
      let _ = Procutils.PrvComms.stop !is_log_all log_file !process  !redlog_call_count 9 ending_fnc in
      is_reduce_running := false
  end

let restart reason =
  if !is_reduce_running then begin
    print_string reason;
    print_endline " Restarting Reduce... "; flush stdout;
    Procutils.PrvComms.restart !is_log_all log_file "redlog" reason start stop
  end

(*
 * send cmd to redlog and get the result from redlog
 * assume result is the next line read from inchannel
 * return empty string if reduce is not running
 *)
let send_and_receive f =
  if !is_reduce_running then
    try
        let fnc () =
          let _ = send_cmd f in
          input_line !process.inchannel
        in
        let fail_with_timeout () =
          restart "Timeout!";
          "" in
        let answ = Procutils.PrvComms.maybe_raise_and_catch_timeout fnc () !timeout fail_with_timeout in
        answ
    with
      | ex ->
        print_endline (Printexc.to_string ex);
        restart "Reduce crashed or something really bad happenned!";
        ""
  else
    ""

	(* send formula to reduce/redlog and receive result *)
let check_formula f =
  let res = send_and_receive ("rlqe " ^ f) in
  if res = "true$" then
    Some true
  else if res = "false$" then
    Some false
  else
    None

(* 
 * run func and return its result together with running time 
 * func must be lazy
 *)
let time func =
  let pre_time = Unix.gettimeofday () in
  let res = Lazy.force func in
  let post_time = Unix.gettimeofday () in
  let time_taken = (post_time -. pre_time) in
  (res, time_taken)

(* call omega's function func and collect the running time *)
let call_omega func =
  let _ = incr omega_call_count in
  let res, time = time func in
  linear_time := !linear_time +. time;
  (*log DEBUG (string_of_float time);*)
  (res, time)

(* call redlog's function func and collect the running time *)
let call_redlog func =
  let _ = incr redlog_call_count in
  let res, time = time func in
  nonlinear_time := !nonlinear_time +. time;
  (*log DEBUG (string_of_float time);*)
  (res, time)

(*
 * run func with timeout checking 
 * return default_val if the running time exceed allowed time
 * also print err_msg when timeout happen
 * func must be lazy
 *)
let run_with_timeout func err_msg =
  let fail_with_timeout () = log ERROR ("TIMEOUT");
    log ERROR err_msg;
    restart ("After timeout"^err_msg);
    None
  in
  let res = Procutils.PrvComms.maybe_raise_and_catch_timeout func () !timeout fail_with_timeout in
  res

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
  | CP.SpecVar (_, v, _) -> v ^ (if CP.is_primed sv then "PRMD" else "")

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
  | _ -> failwith ("redlog: bags/list is not supported")

let rl_of_b_formula b =
  let mk_bin_exp opt e1 e2 = 
    "(" ^ (rl_of_exp e1) ^ opt ^ (rl_of_exp e2) ^ ")"
  in
  let (pf,_) = b in
  match pf with
  | CP.BConst (c, _) -> if c then "true" else "false"
  | CP.BVar (bv, _) -> 
      (* The following solution is just a copy of what omega.ml used. *)
      "(" ^ (rl_of_spec_var bv) ^ " > 0)"
  | CP.Lt (e1, e2, l) -> mk_bin_exp " < " e1 e2
  | CP.Lte (e1, e2, l) -> mk_bin_exp " <= " e1 e2
  | CP.Gt (e1, e2, l) -> mk_bin_exp " > " e1 e2
  | CP.Gte (e1, e2, l) -> mk_bin_exp " >= " e1 e2
  | CP.Eq (e1, e2, _) ->
      (*if CP.is_null e2 then (rl_of_exp e1) ^ " <= 0"*)
      (*else if CP.is_null e1 then (rl_of_exp e2) ^ " <= 0"*)
      (*else*)
      mk_bin_exp " = " e1 e2
  | CP.Neq (e1, e2, _) -> 
      (*if CP.is_null e2 then (rl_of_exp e1) ^ " > 0"*)
      (*else if CP.is_null e1 then (rl_of_exp e2) ^ " > 0"*)
      (*else*)
      mk_bin_exp " <> " e1 e2
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
  | CP.BForm (b,_) -> rl_of_b_formula b 
  | CP.Not (f, _, _) -> "(not " ^ (rl_of_formula f) ^ ")"
  | CP.Forall (sv, f, _, _) -> "(all (" ^ (rl_of_spec_var sv) ^ ", " ^ (rl_of_formula f) ^ "))"
  | CP.Exists (sv, f, _, _) -> "(ex (" ^ (rl_of_spec_var sv) ^ ", " ^ (rl_of_formula f) ^ "))"
  | CP.And (f1, f2, _) -> "(" ^ (rl_of_formula f1) ^ " and " ^ (rl_of_formula f2) ^ ")"
  | CP.Or (f1, f2, _, _) -> "(" ^ (rl_of_formula f1) ^ " or " ^ (rl_of_formula f2) ^ ")"
  
 

(***********************************
 pretty printer for pure formula
 **********************************)
 
let rec string_of_exp e0 =
  let need_parentheses e = match e with
    | CP.Add _ | CP.Subtract _ -> true
    | _ -> false
  in let wrap e =
    if need_parentheses e then "(" ^ (string_of_exp e) ^ ")"
    else (string_of_exp e)
  in
  match e0 with
  | CP.Null _ -> "null"
  | CP.Var (v, _) -> rl_of_spec_var v
  | CP.IConst (i, _) -> string_of_int i
  | CP.FConst (f, _) -> string_of_float f
  | CP.Add (e1, e2, _) -> (string_of_exp e1) ^ "+" ^ (string_of_exp e2)
  | CP.Subtract (e1, e2, _) -> (string_of_exp e1) ^ "-" ^ (string_of_exp e2)
  | CP.Mult (e1, e2, _) -> (wrap e1) ^ "*" ^ (wrap e2)
  | CP.Div (e1, e2, _) -> (wrap e1) ^ "/" ^ (wrap e2)
  | CP.Max (e1, e2, _) -> "max(" ^ (string_of_exp e1) ^ "," ^ (string_of_exp e2) ^ ")"
  | CP.Min (e1, e2, _) -> "min(" ^ (string_of_exp e1) ^ "," ^ (string_of_exp e2) ^ ")"
  | _ -> "???"
  
let string_of_b_formula bf = 
  let build_exp e1 e2 op =
    (string_of_exp e1) ^ op ^ (string_of_exp e2)
  in let (pf,_) = bf in match pf with
    | CP.BConst (b, _) -> (string_of_bool b)
    | CP.BVar (bv, _) -> (rl_of_spec_var bv) ^ " > 0"
    | CP.Lt (e1, e2, _) -> build_exp e1 e2 " < "
    | CP.Lte (e1, e2, _) -> build_exp e1 e2 " <= "
    | CP.Gt (e1, e2, _) -> build_exp e1 e2 " > "
    | CP.Gte (e1, e2, _) -> build_exp e1 e2 " >= "
    | CP.Eq (e1, e2, _) -> build_exp e1 e2 " = "
    | CP.Neq (e1, e2, _) -> build_exp e1 e2 " != "
    | CP.EqMax (e1, e2, e3, _) ->
        (string_of_exp e1) ^ " = max(" ^ (string_of_exp e2) ^ "," ^ (string_of_exp e3) ^ ")"
    | CP.EqMin (e1, e2, e3, _) ->
        (string_of_exp e1) ^ " = min(" ^ (string_of_exp e2) ^ "," ^ (string_of_exp e3) ^ ")"
    | _ -> "???"

let rec string_of_formula f0 = match f0 with
  | CP.BForm (b, _) -> string_of_b_formula b
  | CP.And (f1, f2, _) -> 
      let wrap f = match f with
        | CP.Or _ | CP.BForm _ -> "(" ^ (string_of_formula f) ^ ")"
        | _ -> string_of_formula f
      in
      (wrap f1) ^ " and " ^ (wrap f2)
  | CP.Or (f1, f2, _, _) -> 
      let wrap f = match f with
        | CP.And _ | CP.BForm _ -> "(" ^ (string_of_formula f) ^ ")"
        | _ -> string_of_formula f
      in
      (wrap f1) ^ " or " ^ (wrap f2)
  | CP.Not (f1, _, _) -> "not(" ^ (string_of_formula f1) ^ ")"
  | CP.Forall (sv, f1, _, _) -> "all(" ^ (rl_of_spec_var sv) ^ ", " ^ (string_of_formula f1) ^ ")"
  | CP.Exists (sv, f1, _, _) -> "ex(" ^ (rl_of_spec_var sv) ^ ", " ^ (string_of_formula f1) ^ ")"
  
let simplify_var_name (e: CP.formula) : CP.formula =
  let shorten_sv (CP.SpecVar (typ, name, prm)) vnames =
    let short_name =
      try
        Hashtbl.find vnames name
      with Not_found ->
        let fresh_name = "v" ^ (string_of_int (Hashtbl.length vnames)) in
        let _ = Hashtbl.add vnames name fresh_name in
        fresh_name
    in
    CP.SpecVar (typ, short_name, prm)
  in
  let f_bf vnames bf =
	let (pf,il) = bf in
	match pf with
    | CP.BVar (sv, l) -> Some ((CP.BVar (shorten_sv sv vnames, l)),il)
    | _ -> None
  in
  let f_e vnames e = match e with
    | CP.Var (sv, l) ->
        Some (CP.Var (shorten_sv sv vnames, l))
    | _ -> None
  in
  let rec simplify f0 vnames = match f0 with
    | CP.Forall (sv, f1, lbl, l) ->
        let nsv = shorten_sv sv vnames in
        let nf1 = simplify f1 vnames in
        CP.Forall (nsv, nf1, lbl, l)
    | CP.Exists (sv, f1, lbl, l) ->
        let nsv = shorten_sv sv vnames in
        let nf1 = simplify f1 vnames in
        CP.Exists (nsv, nf1, lbl, l)
    | CP.And (f1, f2, l) ->
        let nf1 = simplify f1 vnames in
        let nf2 = simplify f2 vnames in
        CP.And (nf1, nf2, l)
    | CP.Or (f1, f2, lbl, l) ->
        let nf1 = simplify f1 vnames in
        let nf2 = simplify f2 vnames in
        CP.Or (nf1, nf2, lbl, l)
    | CP.Not (f1, lbl, l) ->
        CP.Not (simplify f1 vnames, lbl, l)
    | CP.BForm (bf, lbl) ->
	    CP.BForm (CP.map_b_formula_arg bf vnames (f_bf, f_e) (idf2, idf2), lbl)
  in
  simplify e (Hashtbl.create 100)

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
  | CP.Div (e1, e2, _) -> false
      (* Omega don't accept / operator, we have to manually transform the formula *)
      (*
      (match e2 with
        | CP.IConst _ -> is_linear_exp e1
        | _ -> false)
      *)
  | _ -> false

let is_linear_bformula b =
  let (pf,_) = b in
  match pf with
  | CP.BConst _ -> true
  | CP.BVar _ -> true
  | CP.Lt (e1, e2, _) | CP.Lte (e1, e2, _) 
  | CP.Gt (e1, e2, _) | CP.Gte (e1, e2, _)
  | CP.Eq (e1, e2, _) | CP.Neq (e1, e2, _)
      -> (is_linear_exp e1) && (is_linear_exp e2)
  | CP.EqMax (e1, e2, e3, _) | CP.EqMin (e1, e2, e3, _)
      -> (is_linear_exp e1) && (is_linear_exp e2) && (is_linear_exp e3)
  | _ -> false
  
let rec is_linear_formula f0 = 
  match f0 with
    | CP.BForm (b,_) -> is_linear_bformula b
    | CP.Not (f, _,_) | CP.Forall (_, f, _,_) | CP.Exists (_, f, _,_) ->
        is_linear_formula f;
    | CP.And (f1, f2, _) | CP.Or (f1, f2, _,_) ->
        (is_linear_formula f1) && (is_linear_formula f2)

let has_var_exp e0 =
  let f e = match e with
    | CP.Var _ -> Some true
    | _ -> None
  in
  CP.fold_exp e0 f or_list 

let is_linear2 f0 =
  let f_bf bf = 
    if CP.is_bag_bform bf || CP.is_list_bform bf then
      Some false
    else None
  in
  let rec f_e e =
    if CP.is_bag e || CP.is_list e then 
      Some false
    else
      match e with
      | CP.Mult (e1, e2, _) -> 
          if (has_var_exp e1 && has_var_exp e2) then
            Some false
          else None
      | CP.Div (e1, e2, _) -> Some false
      | _ -> None
  in
  CP.fold_formula f0 (nonef, f_bf, f_e) and_list

let rec has_existential_quantifier f0 negation_bounded =
  match f0 with 
  | CP.Exists (_, f, _, _) -> 
      if negation_bounded then 
        has_existential_quantifier f negation_bounded 
      else 
        true
  | CP.Forall (_, f, _, _) ->
      if negation_bounded then
        true
      else
        has_existential_quantifier f negation_bounded
  | CP.Not (f, _,  _) -> has_existential_quantifier f (not negation_bounded)
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _, _) -> 
      (has_existential_quantifier f1 negation_bounded) ||
      (has_existential_quantifier f2 negation_bounded)
  | CP.BForm _ -> false

let has_exists2 f0 =
  let f_f neg_bounded e = match e with
    | CP.Exists _ -> if not neg_bounded then Some true else None
    | CP.Forall _ -> if neg_bounded then Some true else None
    | _ -> None
  in
  let f_f_arg neg_bounded e = match e with
    | CP.Not _ -> not neg_bounded
    | _ -> neg_bounded
  in
  let f_bf a e = Some false in
  let f_e a e = Some false in
  CP.fold_formula_arg f0 false (f_f, f_bf, f_e) (f_f_arg, idf2, idf2) or_list

(*
 * e1 < e2 ~> e1 <= e2 -1
 * e1 > e2 ~> e1 >= e2 + 1
 * e1 != e2 ~> e1 >= e2 + 1 or e1 <= e2 - 1
 *) 
 
 let rec strengthen_formula f0 = 
  match f0 with
  | CP.BForm ((pf,il),lbl) -> 
      let r = match pf with
        | CP.Lt (e1, e2, l) -> CP.BForm ((CP.Lte (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l), il), lbl)
        | CP.Gt (e1, e2, l) -> CP.BForm ((CP.Gte (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l), il), lbl)
        | CP.Neq (e1, e2, l) ->
            let lp = CP.Lte (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l) in
            let rp = CP.Gte (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l) in
            CP.Or (CP.BForm ((lp,il), lbl), CP.BForm ((rp,il), lbl), lbl, l)
        | _ -> f0 
      in r
  | CP.Not (f, lbl, l) -> CP.Not (strengthen_formula f, lbl, l)
  | CP.Forall (sv, f, lbl, l) -> CP.Forall (sv, strengthen_formula f, lbl, l)
  | CP.Exists (sv, f, lbl, l) -> CP.Exists (sv, strengthen_formula f, lbl, l)
  | CP.And (f1, f2, l) -> CP.And (strengthen_formula f1, strengthen_formula f2, l)
  | CP.Or (f1, f2, lbl, l) -> CP.Or (strengthen_formula f1, strengthen_formula f2, lbl, l)


let strengthen2 f0 =
  let f_f f =
	match f with
	| CP.BForm ((CP.Neq (e1, e2, l), il), lbl) ->
        let lp = CP.Lte (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l) in
        let rp = CP.Gte (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l) in
        Some (CP.Or (CP.BForm ((lp, il), lbl), CP.BForm ((rp, il), lbl), lbl, l))
    | _ -> None
  in
  let f_bf bf =
	let (pf,il) = bf in
	match pf with
    | CP.Lt (e1, e2, l) -> Some ((CP.Lte (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l)),il)
    | CP.Gt (e1, e2, l) -> Some ((CP.Gte (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l)),il)
    | _ -> Some bf
  in
  CP.map_formula f0 (f_f, f_bf, nonef)

(*
 * e1 <= e2 ~> e1 < e2 + 1
 * e1 >= e2 ~> e1 > e2 - 1
 * e1 = e2 ~> e2 - 1 < e1 < e2 + 1
 *)
 
let rec weaken_formula f0 = 
  match f0 with
  | CP.BForm ((pf,il),lbl) ->
      let r = match pf with
        | CP.Lte (e1, e2, l) -> CP.BForm ((CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l),l), il),lbl)
        | CP.Gte (e1, e2, l) -> CP.BForm ((CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l),l), il),lbl)
        | CP.Eq (e1, e2, l) ->
            let lp = CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l) in
            let rp = CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l) in
            CP.And (CP.BForm ((lp,il),lbl), CP.BForm ((rp,il),lbl), l)
        | _ -> f0 
      in r
  | CP.Not (f,lbl,l) -> CP.Not (weaken_formula f, lbl, l)
  | CP.Forall (sv, f, lbl, l) -> CP.Forall (sv, weaken_formula f, lbl, l)
  | CP.Exists (sv, f, lbl, l) -> CP.Exists (sv, weaken_formula f, lbl, l)
  | CP.And (f1, f2, l) -> CP.And (weaken_formula f1, weaken_formula f2, l)
  | CP.Or (f1, f2, lbl, l) -> CP.Or (weaken_formula f1, weaken_formula f2, lbl, l)

  
let weaken2 f0 =
  let f_f f = match f with
    | CP.BForm ((CP.Eq (e1, e2, l),il), lbl) ->
        let lp = CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l) in
        let rp = CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l) in
        Some (CP.And (CP.BForm ((lp,il),lbl), CP.BForm ((rp,il),lbl), l))
    | _ -> None
  in
  let f_bf bf =
	let (pf,il) = bf in
	match pf with
    | CP.Lte (e1, e2, l) -> Some ((CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l)),il)
    | CP.Gte (e1, e2, l) -> Some ((CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l)),il)
    | _ -> Some bf
  in
  CP.map_formula f0 (f_f, f_bf, nonef)

 (***********************************
 existential quantifier elimination 
 **********************************)

(* using redlog's linear optimization to find bound of a variable in linear formula *)
let find_bound_linear_b_formula v f0 =
  let parse s =
    try
      (* parse the result string from redlog *)
      if s.[0] = '{' then
        let end_pos = String.index s ',' in
        let num = Gen.trim_str (String.sub s 1 (end_pos - 1)) in
        let res = float_of_string num in
        if (abs_float res) = infinity then
          None
        else
          Some res
      else
        None
    with _ -> None
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
  let find_min_cmd = "rlopt({" ^ (rl_of_b_formula f0) ^ "}, " ^ (rl_of_spec_var v) ^ ")" in
  let find_max_cmd = "rlopt({" ^ (rl_of_b_formula f0) ^ "}, -" ^ (rl_of_spec_var v) ^ ")" in
  let _ = send_cmd "on rounded" in
  let min_out = send_and_receive find_min_cmd in
  let max_out = send_and_receive find_max_cmd in
  let _ = send_cmd "off rounded" in
  let min = ceil2 (parse min_out) in
  let max = floor2 (parse max_out) in
  (min, max)

let find_bound_b_formula v b0 =
  if is_linear_bformula b0 then find_bound_linear_b_formula v b0
  else (None, None)

let rec find_bound v f0 =
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
  | CP.BForm (bf,_) -> find_bound_b_formula v bf
  | _ -> None, None
  
and get_subst_min f0 v = match f0 with
  | CP.And (f1, f2, pos) ->
    let st1, rf1 = get_subst_min f1 v in
    if not (Gen.is_empty st1) then
      (st1, CP.mkAnd rf1 f2 pos)
    else
      let st2, rf2 = get_subst_min f2 v in
      (st2, CP.mkAnd f1 rf2 pos)
  | CP.BForm bf -> get_subst_min_b_formula bf v
  | _ -> ([], f0)

and get_subst_min_b_formula (bf,lbl) v =
  let (pf,il) = bf in
  match pf with
  | CP.EqMin (e0, e1, e2, pos) ->
    if CP.is_var e0 then
      let v0 = CP.to_var e0 in
      if CP.eq_spec_var v0 v then
        ([v, e1, e2], CP.mkTrue no_pos)
      else ([], CP.BForm (bf,lbl))
    else ([], CP.BForm (bf,lbl))
  | _ -> ([], CP.BForm (bf,lbl))
  
and get_subst_max f0 v = match f0 with
  | CP.And (f1, f2, pos) ->
    let st1, rf1 = get_subst_max f1 v in
    if not (Gen.is_empty st1) then
      (st1, CP.mkAnd rf1 f2 pos)
    else
      let st2, rf2 = get_subst_max f2 v in
      (st2, CP.mkAnd f1 rf2 pos)
  | CP.BForm bf -> get_subst_max_b_formula bf v
  | _ -> ([], f0)
  
and get_subst_max_b_formula (bf,lbl) v =
  let (pf,_) = bf in
  match pf with
  | CP.EqMax (e0, e1, e2, pos) ->
    if CP.is_var e0 then
      let v0 = CP.to_var e0 in
      if CP.eq_spec_var v0 v then
        ([v, e1, e2], CP.mkTrue no_pos)
      else ([], CP.BForm (bf,lbl))
    else ([], CP.BForm (bf,lbl))
  | _ -> ([], CP.BForm (bf,lbl))
    
(* 
 * partition an expression based on variable v
 * return a tuple (f, rest)
 * e = f*v + rest
 *)
let rec partition_by_var e v =
  match e with
  | CP.Var (sp, _) ->
      if CP.eq_spec_var sp v then
        (1, None)
      else
        (0, Some e)
  | CP.Add (e1, e2, _) ->
      let e1_v, e1_rest = partition_by_var e1 v in
      let e2_v, e2_rest = partition_by_var e2 v in
      let with_v = e1_v + e2_v in
      let without_v = match e1_rest, e2_rest with
        | None, None -> None
        | Some e, None -> e1_rest
        | None, Some e -> e2_rest
        | Some e1, Some e2 -> Some (CP.Add (e1, e2, no_pos))
      in
      (with_v, without_v)
  | CP.Subtract (e1, e2, _) ->
      let e1_v, e1_rest = partition_by_var e1 v in
      let e2_v, e2_rest = partition_by_var e2 v in
      let with_v = e1_v - e2_v in
      let without_v = match e1_rest, e2_rest with
        | None, None -> None
        | Some e, None -> e1_rest
        | None, Some e ->
            let zero = CP.IConst (0, no_pos) in
            Some (CP.Subtract (zero, e, no_pos))
        | Some e1, Some e2 -> Some (CP.Subtract (e1, e2, no_pos))
      in
      (with_v, without_v)
  | _ -> (0, Some e)

let get_subst_equation_b_formula bf0 v lbl =
  let (pf,il) = bf0 in
  match pf with
  | CP.Eq (e1, e2, pos) -> 
      let e = CP.Subtract (e1, e2, no_pos) in
      let with_v, without_v = partition_by_var e v in
      if with_v = 1 then
        let zero = CP.IConst (0, no_pos) in
        let rhs = match without_v with
          | None -> zero
          | Some e -> CP.Subtract (zero, e, no_pos) 
        in
        ([(v, rhs)], CP.mkTrue no_pos)
      else if with_v = -1 then
        let zero = CP.IConst (0, no_pos) in
        let rhs = match without_v with
          | None -> zero
          | Some e -> e
        in
        ([(v, rhs)], CP.mkTrue no_pos)
      else
        ([], CP.BForm (bf0, lbl))
  | _ -> ([], CP.BForm (bf0,lbl))

let rec get_subst_equation f0 v =
  match f0 with
  | CP.And (f1, f2, pos) ->
	  let st1, rf1 = get_subst_equation f1 v in
		if not (Gen.is_empty st1) then
		  (st1, CP.mkAnd rf1 f2 pos)
		else
		  let st2, rf2 = get_subst_equation f2 v in
			(st2, CP.mkAnd f1 rf2 pos)
  | CP.BForm (bf, lbl) -> get_subst_equation_b_formula bf v lbl
  | _ -> ([], f0)

(* base of all elim_exits functions *)
let rec elim_exists_helper core f0 =
  let elim_exists = elim_exists_helper core in
  match f0 with
  | CP.Exists (qvar, qf, lbl, pos) -> 
      let res = match qf with
        | CP.Or (qf1, qf2, lbl2, qpos) ->
            let new_qf1 = CP.mkExists [qvar] qf1 lbl qpos in
            let new_qf2 = CP.mkExists [qvar] qf2 lbl qpos in
            let eqf1 = elim_exists new_qf1 in
            let eqf2 = elim_exists new_qf2 in
            let res = CP.mkOr eqf1 eqf2 lbl2 pos in
            res
        | _ ->
            let qf = elim_exists qf in
            core qvar qf lbl pos
      in res
  | CP.And (f1, f2, pos) -> begin
	  let ef1 = elim_exists f1 in
	  let ef2 = elim_exists f2 in
	  let res = CP.mkAnd ef1 ef2 pos in
		res
	end
  | CP.Or (f1, f2, lbl, pos) -> begin
	  let ef1 = elim_exists f1 in
	  let ef2 = elim_exists f2 in
	  let res = CP.mkOr ef1 ef2 lbl pos in
		res
	end
  | CP.Not (f1, lbl, pos) -> begin
	  let ef1 = elim_exists f1 in
	  let res = CP.mkNot ef1 lbl pos in
		res
	end
  | CP.Forall (qvar, qf, lbl, pos) -> begin
	  let eqf = elim_exists qf in
	  let res = CP.mkForall [qvar] eqf lbl pos in
		res
	end
  | CP.BForm _ -> f0

let rec elim_exists_helper2 core (f0: CP.formula) : CP.formula =
  let f_f f = match f with
    | CP.Exists (qvar, qf, lbl, pos) ->
        let res = match qf with
          | CP.Or (qf1, qf2, lbl2, qpos) ->
              let new_qf1 = CP.mkExists [qvar] qf1 lbl qpos in
              let new_qf2 = CP.mkExists [qvar] qf2 lbl qpos in
              let eqf1 = elim_exists_helper2 core new_qf1 in
              let eqf2 = elim_exists_helper2 core new_qf2 in
              Some (CP.mkOr eqf1 eqf2 lbl2 pos)
          | _ ->
              let qf = elim_exists_helper2 core qf in
              Some (core qvar qf lbl pos)
        in res
    | CP.BForm bf -> Some f
    | _ -> None
  in
  CP.map_formula f0 (f_f, somef, somef)

let rec elim_exists_with_eq f0 = 
  let core qvar qf lbl pos =
    let qf = elim_exists_with_eq qf in
    let qvars0, bare_f = CP.split_ex_quantifiers qf in
    let qvars = qvar :: qvars0 in
    let conjs = CP.list_of_conjs bare_f in
    let no_qvars_list, with_qvars_list = List.partition
    (fun cj -> CP.disjoint qvars (CP.fv cj)) conjs in
    (* the part that does not contain the quantified var *)
    let no_qvars = CP.conj_of_list no_qvars_list pos in
    (* now eliminate the quantified variables from the part that contains it *)
    let with_qvars = CP.conj_of_list with_qvars_list pos in
    (* now eliminate the top existential variable. *)
    let st, pp1 = get_subst_equation with_qvars qvar in
    if not (Gen.is_empty st) then
      let new_qf = CP.subst_term st pp1 in
      let new_qf = CP.mkExists qvars0 new_qf lbl pos in
      let tmp3 = elim_exists_with_eq new_qf in
      let tmp4 = CP.mkAnd no_qvars tmp3 pos in
      tmp4
    else (* if qvar is not equated to any variables, try the next one *)
      let tmp1 = qf (*elim_exists qf*) in
      let tmp2 = CP.mkExists [qvar] tmp1 lbl pos in
      tmp2
  in elim_exists_helper core f0

and elim_exists_min f0 =
  let core qvar qf lbl pos =
    let qvars0, bare_f = CP.split_ex_quantifiers qf in
    let qvars = qvar :: qvars0 in
    let conjs = CP.list_of_conjs qf in
    let no_qvars_list, with_qvars_list = List.partition
    (fun cj -> CP.disjoint qvars (CP.fv cj)) conjs in
    let no_qvars_f = CP.conj_of_list no_qvars_list pos in
    let with_qvars_f = CP.conj_of_list with_qvars_list pos in
    let st, pp1 = get_subst_min with_qvars_f qvar in
    if not (Gen.is_empty st) then
      let v, e1, e2 = List.hd st in
      let tmp1 = 
        CP.mkOr 
        (CP.mkAnd (CP.mkAnd (CP.mkEqExp (CP.mkVar v pos) e1 pos) (CP.BForm (((CP.mkLte e1 e2 pos), None),None)) pos) pp1 pos)
        (CP.mkAnd (CP.mkAnd (CP.mkEqExp (CP.mkVar v pos) e2 pos) (CP.BForm (((CP.mkGt e1 e2 pos), None),None)) pos) pp1 pos)
        None
        pos
      in
      let tmp2 = CP.elim_exists (CP.mkExists [qvar] tmp1 lbl pos) in
      let tmp3 = CP.mkExists qvars0 tmp2 None pos in
      let tmp4 = elim_exists_min tmp3 in
      let new_qf = CP.mkAnd no_qvars_f tmp4 pos in
      new_qf
    else
      CP.mkExists [qvar] qf lbl pos
  in elim_exists_helper core f0

and elim_exists_max f0 =
  let core qvar qf lbl pos =
    let qvars0, bare_f = CP.split_ex_quantifiers qf in
    let qvars = qvar :: qvars0 in
    let conjs = CP.list_of_conjs qf in
    let no_qvars_list, with_qvars_list = List.partition
    (fun cj -> CP.disjoint qvars (CP.fv cj)) conjs in
    let no_qvars_f = CP.conj_of_list no_qvars_list pos in
    let with_qvars_f = CP.conj_of_list with_qvars_list pos in
    let st, pp1 = get_subst_max with_qvars_f qvar in
    if not (Gen.is_empty st) then
      let v, e1, e2 = List.hd st in
      let tmp1 = 
        CP.mkOr 
        (CP.mkAnd (CP.mkAnd (CP.mkEqExp (CP.mkVar v pos) e1 pos) (CP.BForm (((CP.mkGte e1 e2 pos), None),None) ) pos) pp1 pos)
        (CP.mkAnd (CP.mkAnd (CP.mkEqExp (CP.mkVar v pos) e2 pos) (CP.BForm (((CP.mkLt e1 e2 pos), None),None) ) pos) pp1 pos)
        None
        pos
      in
      let tmp2 = CP.elim_exists (CP.mkExists [qvar] tmp1 lbl pos) in
      let tmp3 = CP.mkExists qvars0 tmp2 None pos in
      let tmp4 = elim_exists_max tmp3 in
      let new_qf = CP.mkAnd no_qvars_f tmp4 pos in
      new_qf
      else
        CP.mkExists [qvar] qf lbl pos
  in elim_exists_helper core f0
  
let rec elim_exists_with_ineq f0 =
  let core qvar qf lbl pos =
    let min, max = find_bound qvar qf in
    begin
      match min, max with
      | Some mi, Some ma ->
          let res = ref (CP.mkFalse pos) in
          begin
            for i = mi to ma do
              res := CP.mkOr !res (CP.apply_one_term (qvar, CP.IConst (i, no_pos)) qf) lbl pos
            done;
            !res
          end
      | _ -> f0
    end
  in elim_exists_helper core f0

let elim_exist_quantifier f =
  let _ = incr ee_call_count in
  let f = elim_exists_with_eq f in
  let f = elim_exists_min f in
  let f = elim_exists_max f in
  let f = elim_exists_with_ineq f in 
  f

(*********************************
 * formula normalization stuffs
 * *******************************)

let negate_b_formula bf0 =
  let (pf,il) = bf0 in
  let npf = match pf with
  | CP.BConst (b, pos) -> Some (CP.BConst (not b, pos))
  | CP.BVar (sv, pos) -> None
  | CP.Lt (e1, e2, pos) -> Some (CP.Gte (e1, e2, pos))
  | CP.Lte (e1, e2, pos) -> Some (CP.Gt (e1, e2, pos))
  | CP.Gt (e1, e2, pos) -> Some (CP.Lte (e1, e2, pos))
  | CP.Gte (e1, e2, pos) -> Some (CP.Lt (e1, e2, pos))
  | CP.Eq (e1, e2, pos) -> Some (CP.Neq (e1, e2, pos))
  | CP.Neq (e1, e2, pos) -> Some (CP.Eq (e1, e2, pos))
  | _ -> None
  in match npf with
	| None -> None
	| Some pf -> Some (pf,il)
  
let rec negate_formula f0 = match f0 with
  | CP.BForm (bf, lbl) ->
    let neg_bf = negate_b_formula bf in
    let res = match neg_bf with
    | Some new_bf -> CP.BForm (new_bf, lbl)
    | None -> CP.Not (CP.BForm (bf, lbl), None, no_pos)
    in res
  | CP.And (f1, f2, pos) -> CP.Or (negate_formula f1, negate_formula f2, None, pos)
  | CP.Or (f1, f2, lbl, pos) -> CP.And (negate_formula f1, negate_formula f2, pos)
  | CP.Not (f, lbl, pos) -> f
  | CP.Forall (sv, f, lbl, pos) -> CP.Exists (sv, negate_formula f, lbl, pos)
  | CP.Exists (sv, f, lbl, pos) -> CP.Forall (sv, negate_formula f, lbl, pos)
  
let rec normalize_formula f0 = match f0 with
  | CP.BForm _ -> f0
  | CP.And (f1, f2, pos) -> CP.And (normalize_formula f1, normalize_formula f2, pos)
  | CP.Or (f1, f2, lbl, pos) -> CP.Or (normalize_formula f1, normalize_formula f2, lbl, pos)
  | CP.Not (f1, lbl, pos) -> negate_formula f1
  | CP.Forall (sv, f, lbl, pos) -> CP.Forall (sv, normalize_formula f, lbl, pos)
  | CP.Exists (sv, f, lbl, pos) -> CP.Exists (sv, normalize_formula f, lbl, pos)

(**********************
   Verification works  
 *********************)

(* to check whether a formula is satisfiable or not
 * using existence enclosure (rlex) for all free vars
 *)

let options_to_bool opts default =
  match opts with
  | Some opt ->
      let res = match opt with
        | Some v -> v
        | None -> default
      in res
  | None -> default

let is_sat_no_cache (f: CP.formula) (sat_no: string) : bool * float =
  if is_linear_formula f then
    call_omega (lazy (Omega.is_sat f sat_no))
  else
	let _ = Gen.Profiling.inc_counter "stat_redlog_count_sat" in
    let sf = if !no_pseudo_ops then f else strengthen_formula f in
    let frl = rl_of_formula sf in
    let rl_input = "rlex(" ^ frl ^ ")" in
    let runner () = check_formula rl_input in
    let err_msg = "Timeout when checking #is_sat " ^ sat_no ^ "!" in
    let proc =  lazy (run_with_timeout runner err_msg) in
    let res, time = call_redlog proc in
    let sat = options_to_bool (Some res) true in (* default is SAT *)
    (sat, time)

let is_sat f sat_no =
  let sf = simplify_var_name (normalize_formula f) in
  let fstring = string_of_formula sf in
  log DEBUG ("\n#is_sat " ^ sat_no);
  log DEBUG fstring;
  let res = 
    if !no_cache then
      fst (is_sat_no_cache f sat_no)
    else
      try
        let res = Hashtbl.find !sat_cache fstring in
        incr cached_count;
        log DEBUG "Cached.";
        res
      with Not_found ->
		let _ = Gen.Profiling.inc_counter "sat_proof_count_no_cache_redlog" in
        let res, time = is_sat_no_cache f sat_no in
        let _ = if time > cache_threshold then
          Hashtbl.add !sat_cache fstring res 
        in res
  in
  log DEBUG (if res then "SAT" else "UNSAT");
  res

let is_valid f imp_no =
  let f = normalize_formula f in
  let frl = rl_of_formula f in
  let rl_input = "rlall(" ^ frl ^")" in
  let runner () = check_formula rl_input in
  let err_msg = "Timeout when checking #imply " ^ imp_no ^ "!" in
  let proc = lazy (run_with_timeout runner err_msg) in
  let res, time = call_redlog proc in
  let valid = options_to_bool (Some res) false in (* default is INVALID *)
  (valid, time)

let imply_no_cache (f : CP.formula) (imp_no: string) : bool * float =
  let has_eq f = has_existential_quantifier f false in
  let elim_eq f =
    if !no_elim_exists then f else elim_exist_quantifier f
  in
  let valid f = 
    let wf = if !no_pseudo_ops then f else weaken_formula f in
    is_valid wf imp_no    in
   let res = 
    if is_linear_formula f then
      call_omega (lazy (Omega.is_valid f !timeout))
    else
	  let _ = Gen.Profiling.inc_counter "stat_redlog_count_imply" in
      if has_eq f then
        let eef = elim_eq f in
        if has_eq eef then
          (print_string ("\nWARNING: Found formula with existential quantified var(s), result may be unsound! (Imply #" ^ imp_no ^ ") for redlog");
          valid eef)
        else
          let _ = incr success_ee_count in
          valid eef
      else valid f
  in
  res

let imply ante conseq imp_no =
  let f = normalize_formula (CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos) in
  let sf = simplify_var_name f in
  let fstring = string_of_formula sf in
  log DEBUG ("\n#imply " ^ imp_no);
  log DEBUG ("ante: " ^ (string_of_formula ante));
  log DEBUG ("conseq: " ^ (string_of_formula conseq));
  let res = 
    if !no_cache then
      fst (imply_no_cache f imp_no)
    else
      try
        let res = Hashtbl.find !impl_cache fstring in
        incr cached_count;
        log DEBUG "Cached.";
        res
      with Not_found ->
		let _ = Gen.Profiling.inc_counter "imply_proof_count_no_cache_redlog" in
        let res, time = imply_no_cache f imp_no in
        let _ = if time > cache_threshold then
          Hashtbl.add !impl_cache fstring res
        in res
  in
  log DEBUG (if res then "VALID" else "INVALID");
  res

let simplify (f: CP.formula) : CP.formula =
  if is_linear_formula f then 
    Omega.simplify f 
  else if !no_simplify then 
    f
   else
    try
      let rlf = rl_of_formula (normalize_formula f) in
      let _ = send_cmd "rlset pasf" in
      let redlog_result = send_and_receive ("rlsimpl " ^ rlf) in
      let _ = send_cmd "rlset ofsf" in
      let lexbuf = Lexing.from_string redlog_result in
      let simpler_f = Rlparser.input Rllexer.tokenizer lexbuf in
      let simpler_f = 
        if is_linear_formula simpler_f then
          Omega.simplify simpler_f
        else
          simpler_f
      in
      log DEBUG "\n#simplify";
      log DEBUG ("original: " ^ (string_of_formula f));
      log DEBUG ("simplified: " ^ (string_of_formula simpler_f));
      simpler_f
    with _ as e -> 
      log ERROR "Error while simplifying with redlog";
      log ERROR (Printexc.to_string e);
      f

(* unimplemented *)

let hull (f: CP.formula) : CP.formula = 
  if is_linear_formula f then 
    Omega.hull f 
  else 
    f

let pairwisecheck (f: CP.formula): CP.formula =
  if is_linear_formula f then 
    Omega.pairwisecheck f 
  else 
    f
