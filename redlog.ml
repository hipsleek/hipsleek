(*
 * Interact with reduce/redlog
 * Created on Aug 31, 2009
 *)

open Globals
module CP = Cpure

let is_log_all = ref false
let is_presburger = ref false
let is_reduce_running = ref false
let log_file = open_out ("allinput.rl")
let reduce = "redcsl"
let in_filename = "input.red." ^ (string_of_int (Unix.getpid ()))
let re_filename = "result.txt." ^ (string_of_int (Unix.getpid ()))
let channels = ref (stdin, stdout)

(**********************
 * auxiliari function *
 **********************)

let log_all string = 
  if !is_log_all then begin
    output_string log_file (string ^ Util.new_line_str);
    flush log_file
  end

let set_timer tsecs =
  ignore (Unix.setitimer Unix.ITIMER_REAL
      {Unix.it_interval = 0.0; Unix.it_value = tsecs})

let remove_tmp_file () =
  try
    ignore (Sys.remove in_filename);
    ignore (Sys.remove re_filename)
  with e -> ignore e

(* start Reduce system in a separated process *)
let start_red () =
  if not !is_reduce_running then begin
    print_string "Starting Reduce/Redlog...\n";
    flush stdout;
    channels := Unix.open_process (reduce ^ " -w 2>/dev/null");
    is_reduce_running := true;
    output_string (snd !channels) "load_package redlog;\n";
    if !is_presburger then
      output_string (snd !channels) "rlset pasf;\n"
    else
      output_string (snd !channels) "rlset ofsf;\n";
    output_string (snd !channels) "on rlnzden;\n"
  end

(* stop Reduce system *)
let stop_red () = 
  if !is_reduce_running then begin
    output_string (snd !channels) "quit;\n";
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
      end
    done;
    !result
  with _ -> 
    ignore (Unix.close_process !channels);
    is_reduce_running := false;
    print_endline "Reduce crashed or something really bad happenned! Restarting...";
    start_red ();
    false

(* parse reduce/redlog's output file *)
let get_result () =
  let last_line = ref "" in
  let last_line2 = ref "" in
  let in_file = open_in re_filename in
  begin
    try
      while true do
        let line = input_line in_file in
        let length = String.length line in
        if length > 0 then begin
          last_line2 := !last_line;
          last_line := line
        end
      done
    with End_of_file -> ();
  end;
  close_in in_file;
  remove_tmp_file ();
  log_all ("[reduce/redlog] => " ^ !last_line2);
  let result = if (!last_line2 = "true") then true else false in
  result

(* run reduce with timeout checking *)
let run_reduce (input: string) : bool =
  let header = "load_package redlog; rlset " 
                ^ (if !is_presburger then "pasf" else "ofsf") ^ ";" 
                ^ " on rlnzden;"
                ^ Util.new_line_str in
  let in_file = open_out in_filename in
  output_string in_file (header ^ input);
  close_out in_file;
  let pid = Unix_add.open_proc reduce [|reduce; "-w"; in_filename|] re_filename in
  let oldsig = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Exit)) in
  let r = try
    begin
      set_timer !Globals.sat_timeout;
      ignore (Unix.waitpid [] pid);
      true
    end
  with Exit ->
    begin
      print_endline "\nReduce timeout reached.";
      flush stdout;
      Unix.kill pid 9;
      ignore (Unix.waitpid [] pid);
      false
    end
  in
  set_timer 0.0;
  Sys.set_signal Sys.sigalrm oldsig;
  let result = if r then get_result () else false in
  result

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
  | CP.Lt (e1, e2, _) -> mk_bin_exp " < " e1 e2
  | CP.Lte (e1, e2, _) -> mk_bin_exp " <= " e1 e2
  | CP.Gt (e1, e2, _) -> mk_bin_exp " > " e1 e2
  | CP.Gte (e1, e2, _) -> mk_bin_exp " >= " e1 e2
  | CP.Eq (e1, e2, _) -> mk_bin_exp " = " e1 e2
  | CP.Neq (e1, e2, _) -> mk_bin_exp " <> " e1 e2
  | CP.EqMax (e1, e2, e3, _) ->
      (* e1 = max(e2,e2) <-> ((e1 = e2 /\ e2 >= e3) \/ (e1 = e3 /\ e2 < e3)) *)
      let a1 = rl_of_exp e1 in
      let a2 = rl_of_exp e2 in
      let a3 = rl_of_exp e3 in
      "((" ^ a1 ^ " = " ^ a2 ^ " and " ^ a2 ^ " >= " ^ a3 ^ ") or ("
      ^ a1 ^ " = " ^ a3 ^ " and " ^ a2 ^ " < " ^ a3 ^ "))"
  | CP.EqMin (e1, e2, e3, _) ->
      (* e1 = min(e2,e3) <-> ((e1 = e2 /\ e2 <= e3) \/ (e1 = e3 /\ e2 > e3)) *)
      let a1 = rl_of_exp e1 in
      let a2 = rl_of_exp e2 in
      let a3 = rl_of_exp e3 in
      "((" ^ a1 ^ " = " ^ a2 ^ " and " ^ a2 ^ " <= " ^ a3 ^ ") or ("
      ^ a1 ^ " = " ^ a3 ^ " and " ^ a2 ^ " > " ^ a3 ^ "))"
  | _ -> failwith "redlog: bags is not supported"

let rec rl_of_formula f0 = 
  match f0 with
  | CP.BForm b -> rl_of_b_formula b
  | CP.Not (f, _) -> "(not " ^ (rl_of_formula f) ^ ")"
  | CP.Forall (sv, f, _) -> "(all (" ^ (rl_of_spec_var sv) ^ ", " ^ (rl_of_formula f) ^ "))"
  | CP.Exists (sv, f, _) -> "(ex (" ^ (rl_of_spec_var sv) ^ ", " ^ (rl_of_formula f) ^ "))"
  | CP.And (f1, f2, _) -> "(" ^ (rl_of_formula f1) ^ " and " ^ (rl_of_formula f2) ^ ")"
  | CP.Or (f1, f2, _) -> "(" ^ (rl_of_formula f1) ^ " or " ^ (rl_of_formula f2) ^ ")"

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
  log_all (if sat then "SUCCESS" else "FAIL");
  sat

let imply (ante : CP.formula) (conseq: CP.formula) (imp_no: string) : bool =
  log_all (Util.new_line_str ^ "#imply " ^ imp_no);
  log_all ("ante: " ^ (Cprinter.string_of_pure_formula ante));
  log_all ("conseq: " ^ (Cprinter.string_of_pure_formula conseq));
  let frl = "(" ^ (rl_of_formula ante) ^ " impl " ^ (rl_of_formula conseq) ^ ")" in
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

(* just prototype *)
let simplify (f: CP.formula) : CP.formula =
    let frl = rl_of_formula f in
    log_all (Util.new_line_str ^ "#simplify");
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

