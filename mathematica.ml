#include "xdebug.cppo"
(*
 * Interact with Mathematica
 * Created on June 23, 2012
 *)

open Globals
open VarGen
open GlobProver
open Gen.Basic
module CP = Cpure

(* options *)
let is_presburger = ref false
let no_pseudo_ops = ref false
let no_elim_exists = ref false
let no_simplify = ref false
let no_cache = ref true
let timeout = ref 10.0 (* default timeout is 15 seconds *)

(* logging *)
let is_log_all = ref false
let log_file = open_log_out "allinput.math"

(* process management *)
let is_mathematica_running = ref false

(* cache *)
(* let sat_cache = ref (Hashtbl.create 100) *)
let impl_cache = ref (Hashtbl.create 100)
(* threshold for caching *)
let cache_threshold = 0.001 (* 1ms *)

(* data collecting stuffs *)
let omega_call_count = ref 0
let mathematica_call_count = ref 0
let ee_call_count = ref 0
let success_ee_count = ref 0
let nonlinear_time = ref 0.0
let linear_time = ref 0.0
let cached_count = ref 0

let mathematica_prompt = "^In[0-9]:= $"

let process = ref {name = "MATHEMATICA"; pid = 0;  inchannel = stdin; outchannel = stdout; errchannel = stdin}

let print_b_formula = ref (fun (c:CP.b_formula) -> "cpure printer has not been initialized")
let print_p_formula = ref (fun (c:CP.p_formula) -> "cpure printer has not been initialized")
let print_exp = ref (fun (c:CP.exp) -> "cpure printer has not been initialized")
let print_formula = ref (fun (c:CP.formula) -> "cpure printer has not been initialized")
let print_svl = ref (fun (c:CP.spec_var list) -> "cpure printer has not been initialized")
let print_sv = ref (fun (c:CP.spec_var) -> "cpure printer has not been initialized")


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

(* Wait and read the output channel of mathematica process until it is ready to work *)
let rec wait_for_ready_prover (channel: in_channel)  =
  let line = input_line channel in
  (* let () = print_endline ("== in wait_for_ready_prover: line = " ^ line) in *)
  let line = Gen.trim_str line in
  if (line = "") then ()
  else (wait_for_ready_prover channel)

let rec read_output (channel: in_channel) : string =
  let line = input_line channel in
  (* let () = print_endline ("== in read_output: line = " ^ line) in *)
  let line = Gen.trim_str line in
  if (((String.length line) > 3) && ((String.sub line 0 4) = "Out[")) then line
  else (read_output channel)

(*
 * send cmd to mathematica
 *)
let send_cmd cmd =
  if !is_mathematica_running then (
    let () = output_string !process.outchannel cmd in
    let () = flush !process.outchannel in
    ()
  )

(* start mathematica in a separated process *)
let start () =
  if not !is_mathematica_running then (
    let prelude () = (
      is_mathematica_running := true;
    ) in
    let set_process proc = process := proc in
    let () = Procutils.PrvComms.start !is_log_all log_file ("math", "math",  [||] ) set_process prelude in
    print_endline_quiet "Starting mathematica... "; flush stdout;
    wait_for_ready_prover !process.inchannel;
    print_endline_quiet ("Mathematica started successfully!");
  )

(* stop mathematica system *)
let stop () =
  if !is_mathematica_running then (
    let ending_fnc () = (
      let outchannel = !process.outchannel in
      output_string outchannel "Quit\n"; flush outchannel;
      print_endline_quiet "Halting mathematica... "; flush stdout;
      log DEBUG "\n***************";
      log DEBUG ("Number of Omega calls: " ^ (string_of_int !omega_call_count));
      log DEBUG ("Number of mathematica calls: " ^ (string_of_int !mathematica_call_count));
      log DEBUG ("Number of formulas that need ee: " ^ (string_of_int !ee_call_count));
      log DEBUG ("Number of successful ee calls: " ^ (string_of_int !success_ee_count));
      log DEBUG ("Number of cached hit: " ^ (string_of_int !cached_count));
      log DEBUG ("Nonlinear verification time: " ^ (string_of_float !nonlinear_time));
      log DEBUG ("Linear verification time: " ^ (string_of_float !linear_time))
    ) in
    let () = Procutils.PrvComms.stop !is_log_all log_file !process  !mathematica_call_count 9 ending_fnc in
    is_mathematica_running := false
  )

let restart reason =
  if !is_mathematica_running then (
    print_string reason;
    print_endline_quiet " Restarting mathematica... "; flush stdout;
    Procutils.PrvComms.restart !is_log_all log_file "mathematica" reason start stop
  )

(*
 * send cmd to mathematica and get the result from mathematica
 * assume result is the next line read from inchannel
 * return empty string if mathematica is not running
 *)
let send_and_receive (f : string) : string =
  if !is_mathematica_running then (
    try
      let fnc () = (
        let () = send_cmd f in
        read_output !process.inchannel
      ) in
      let fail_with_timeout () = (
        restart "Timeout!";
        ""
      ) in
      let answ = Procutils.PrvComms.maybe_raise_and_catch_timeout fnc () !timeout fail_with_timeout in
      answ
    with
    | ex ->
      print_endline_quiet (Printexc.to_string ex);
      (restart "mathematica crashed or something really bad happenned!"; "mathematica not running 1")
  )
  else (
    (restart "mathematica has not started!!"; "mathematica not running 2")
  )

(* send formula to mathematica and receive result *)
let send_and_receive (f : string) : string =
  Debug.no_1 "send_and_receive" (fun s -> s) (fun s -> s) send_and_receive f

let check_formula (f: string) : bool option =
  let output = send_and_receive f in
  try
    (* Output's format has to be "Out[...]= True" or "Out[...]= False" *)
    let result_index = (String.rindex output ' ') + 1 in
    let length = (String.length output) - result_index in
    let result = String.sub output result_index length in
    if (result = "True") then
      Some true
    else if (result = "False") then
      Some false
    else
      let () = x_dinfo_pp ("Mathematica unexpected anser 1: ") no_pos in
      let () = x_dinfo_zp (lazy (("   Input : " ^ f))) no_pos in
      let () = x_dinfo_zp (lazy (("   Output: " ^ output))) no_pos in
      failwith "Mathematica: Unexpected answer!"
  with _ ->
    let () = x_dinfo_pp ("Mathematica unexpected anser 2: ") no_pos in
    let () = x_dinfo_zp (lazy (("   Input : " ^ f))) no_pos in
    let () = x_dinfo_zp (lazy (("   Output: " ^ output))) no_pos in
    failwith "Mathematica: Unexpected answer!"

let check_formula f =
  Debug.no_1 "check_formula" (fun s -> s) (pr_option string_of_bool) check_formula f

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
  let () = incr omega_call_count in
  let res, time = time func in
  linear_time := !linear_time +. time;
  (*log DEBUG (string_of_float time);*)
  (res, time)

(* call mathematica's function func and collect the running time *)
let call_mathematica func =
  let () = incr mathematica_call_count in
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
  let fail_with_timeout () = (
    log ERROR ("TIMEOUT");
    log ERROR err_msg;
    restart ("After timeout"^err_msg);
    None
  ) in
  let res = Procutils.PrvComms.maybe_raise_and_catch_timeout func () !timeout fail_with_timeout in
  res

(**************************
 * cpure to mathematica *
 **************************)

let rec math_of_var_list (vars : ident list) : string =
  match vars with
  | [] -> ""
  | [v] -> v
  | v :: rest -> v ^ ", " ^ (math_of_var_list rest)

let normalize_var_name (varname : string) : string =
  let varname_bytes = Bytes.of_string varname in
  for i = 0 to (Bytes.length varname_bytes) - 1 do
    if Bytes.get varname_bytes i = '_' then varname_bytes.[i] <- 'N'
  done;
  Bytes.to_string varname_bytes



let math_of_float (f: float) =
  let res = Printf.sprintf "%.8f" f in
  res

let math_of_spec_var (v: CP.spec_var) =
  match v with
  | CP.SpecVar (_, sv, prime) ->
    (* mathematica doesn't allow var name contains underscore '_'                        *)
    (* so convert variable name from underscore style to capitalizing-first-letter style *)
    let new_sv = ref "" in
    let to_uppercase = ref false in
    for i = 0 to (String.length sv) - 1 do
      if sv.[i] = '_' then
        to_uppercase := true
      else (
        let s = if not !to_uppercase then
            Char.escaped sv.[i]
          else if (sv.[i] >= '0' && sv.[i] <= '9') then
            "N" ^ Char.escaped (sv.[i])
          else
            Char.escaped (Char.uppercase sv.[i]) in
        new_sv := !new_sv ^ s;
        to_uppercase := false
      )
    done;
    if (prime = Primed) then new_sv := !new_sv ^ "P";
    !new_sv

let rec math_of_exp e0 : string=
  match e0 with
  | CP.Null _ -> "0"
  | CP.Var (v, _) -> math_of_spec_var v
  | CP.Bptriple _ -> failwith ("mathematica.math_of_exp: Bptriple can't appear here")
  | CP.Tup2 _ -> failwith ("mathematica.math_of_exp: Tup2 can't appear here")
  | CP.IConst (i, _) -> string_of_int i
  | CP.AConst (i, _) -> string_of_int (int_of_heap_ann i)
  | CP.FConst (f, _) -> math_of_float f
  | CP.Tsconst _ -> failwith ("mathematica.math_of_exp: Tsconst can't appear here")
  | CP.Add (e1, e2, _) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " + " ^ se2 ^ ")"
  | CP.Subtract (e1, e2, _) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " - " ^ se2 ^ ")"
  | CP.Mult (e1, e2, _) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " * " ^ se2 ^ ")"
  | CP.Div (e1, e2, _) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " / " ^ se2 ^ ")"
  | CP.TypeCast (t, e1, _) -> (
      match t with
      | Globals.Int -> ("IntegerPart[" ^ (math_of_exp e1) ^ "]")
      | Globals.Float -> math_of_exp e1
      | _ -> failwith ("mathematica.math_of_exp: don't support type casting to '"
                       ^ (Globals.string_of_typ t) ^ "'")
    )
  | CP.Max _
  | CP.Min _ -> failwith ("mathematica.math_of_exp: min/max can't appear here")
  | CP.Bag _
  | CP.BagUnion _
  | CP.BagIntersect _
  | CP.BagDiff _  -> failwith ("mathematica.math_of_exp: cannot handle bag operator")
  (* list expressions *)
  | CP.List _
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListAppend _
  | CP.ListReverse _ -> failwith ("mathematica.math_of_exp: cannot handle list operator")
  | CP.ArrayAt _ -> failwith ("mathematica.math_of_exp: cannot handle array operator")
  | CP.Func _ -> failwith ("mathematica.math_of_exp: cannot handle func operator")
  | CP.Level _  -> failwith ("mathematica.math_of_exp: cannot handle Level operator")
  | CP.NegInfConst _
  | CP.InfConst _  -> failwith ("mathematica.math_of_exp: cannot handle InfConst operator")
  | CP.Template t -> math_of_exp (CP.exp_of_template t)

let rec math_of_b_formula b : string =
  let (pf,_) = b in
  match pf with
  | CP.Frm (fv, _) -> "(" ^ math_of_spec_var fv ^ " > 0)"
  | CP.BConst (c, _) ->
    if c then "True"
    else "False"
  | CP.BVar (bv, _) -> "(" ^ math_of_spec_var bv ^ " > 0)"
  | CP.Lt (e1, e2, l) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " < " ^ se2 ^ ")"
  | CP.Lte (e1, e2, l) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " <= " ^ se2 ^ ")"
  | CP.SubAnn (e1, e2, l) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " <= " ^ se2 ^ ")"
  | CP.Gt (e1, e2, l) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " > " ^ se2 ^ ")"
  | CP.Gte (e1, e2, l) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " >= " ^ se2 ^ ")"
  | CP.Eq (e1, e2, _) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " == " ^ se2 ^ ")"
  | CP.Neq (e1, e2, _) ->
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    "(" ^ se1 ^ " != " ^ se2 ^ ")"
  | CP.EqMax (e1, e2, e3, _) ->
    (* e1 = max(e2,e2) <-> ((e1 = e2 /\ e2 >= e3) \/ (e1 = e3 /\ e2 < e3)) *)
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    let se3 = math_of_exp e3 in
    ("((" ^ se1 ^ " == " ^ se2 ^ " && " ^ se2 ^ " >= " ^ se3 ^ ") || "
     ^ "(" ^ se1 ^ " == " ^ se3 ^ " && " ^ se2 ^ " <= " ^ se3 ^ "))")
  | CP.EqMin (e1, e2, e3, _) ->
    (* e1 = min(e2,e3) <-> ((e1 = e2 /\ e2 <= e3) \/ (e1 = e3 /\ e2 > e3)) *)
    let se1 = math_of_exp e1 in
    let se2 = math_of_exp e2 in
    let se3 = math_of_exp e3 in
    ("((" ^ se1 ^ " == " ^ se2 ^ " && " ^ se2 ^ " <= " ^ se3 ^ ") || "
     ^ "(" ^ se1 ^ " == " ^ se3 ^ " && " ^ se2 ^ " >= " ^ se3 ^ "))")
  | CP.XPure _ -> failwith ("math_of_b_formula: cannot handle XPure formula")
  | CP.LexVar _
  | CP.BagIn _
  | CP.BagNotIn _
  | CP.BagSub _
  | CP.BagMin _
  | CP.BagMax _
  (* | CP.VarPerm _ *)
  | CP.ListIn _
  | CP.ListNotIn _
  | CP.ListAllN _
  | CP.ListPerm _
  | CP.ImmRel _
  | CP.RelForm _ -> failwith ("math_of_b_formula: cannot handle bag, list, rel, perm formula")

let rec math_of_formula pr_w pr_s f0 : string =
  let rec formula_to_string f0 = (
    match f0 with
    | CP.BForm ((b,_) as bf,_) -> (
        match (pr_w b) with
        | None -> math_of_b_formula bf
        | Some f -> formula_to_string f
      )
    | CP.AndList _ -> Gen.report_error no_pos "mathematica.ml: encountered AndList, should have been already handled"
    | CP.Not (f, _, _) ->
      let sf = math_of_formula pr_s pr_w f in
      "!( " ^ sf ^ ")"
    | CP.Forall (v, f, _, _) ->
      let sv = math_of_spec_var v in
      let sf = formula_to_string f in
      "ForAll[" ^ sv ^ "," ^ sf ^ "]"
    | CP.Exists (v, f, _, _) ->
      let sv = math_of_spec_var v in
      let sf = formula_to_string f in
      "Exists[" ^ sv ^ "," ^ sf ^ "]"
    | CP.And (f1, f2, _) ->
      let sf1 = formula_to_string f1 in
      let sf2 = formula_to_string f2 in
      "(" ^ sf1 ^ " && " ^ sf2 ^ ")"
    | CP.Or (f1, f2, _, _) ->
      let sf1 = formula_to_string f1 in
      let sf2 = formula_to_string f2 in
      "(" ^ sf1 ^ " || " ^ sf2 ^ ")"
  ) in
  formula_to_string f0

(***********************************
   pretty printer for pure formula
 **********************************)
let string_of_exp e0 = !print_exp e0

let string_of_b_formula bf = !print_b_formula bf

let string_of_formula f0 = !print_formula f0

let simplify_var_name (e: CP.formula) : CP.formula =
  let shorten_sv (CP.SpecVar (typ, name, prm)) vnames = (
    let short_name = (
      try
        Hashtbl.find vnames name
      with
      | Not_found ->
        let fresh_name = "v" ^ (string_of_int (Hashtbl.length vnames)) in
        let () = Hashtbl.add vnames name fresh_name in
        fresh_name
    ) in
    CP.SpecVar (typ, short_name, prm)
  ) in
  let f_bf vnames bf =
    let (pf,il) = bf in
    match pf with
    | CP.BVar (sv, l) -> Some ((CP.BVar (shorten_sv sv vnames, l)),il)
    | _ -> None in
  let f_e vnames e =
    match e with
    | CP.Var (sv, l) -> Some (CP.Var (shorten_sv sv vnames, l))
    | _ -> None in
  let rec simplify f0 vnames =
    match f0 with
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
    | CP.AndList _ -> Gen.report_error no_pos "mathematica.ml: encountered AndList, should have been already handled"
    | CP.Or (f1, f2, lbl, l) ->
      let nf1 = simplify f1 vnames in
      let nf2 = simplify f2 vnames in
      CP.Or (nf1, nf2, lbl, l)
    | CP.Not (f1, lbl, l) -> CP.Not (simplify f1 vnames, lbl, l)
    | CP.BForm (bf, lbl) ->
      CP.BForm (CP.map_b_formula_arg bf vnames (f_bf, f_e) (idf2, idf2), lbl) in
  simplify e (Hashtbl.create 100)

let rec is_linear_exp exp =
  match exp with
  | CP.Null _ | CP.Var _ | CP.IConst _ | CP.AConst _ -> true
  | CP.Add (e1, e2, _) | CP.Subtract (e1, e2, _) -> (is_linear_exp e1) && (is_linear_exp e2)
  | CP.Mult (e1, e2, _) -> (
      match e1 with
      | CP.IConst _ -> is_linear_exp e2
      | _ -> (match e2 with
          | CP.IConst _ -> is_linear_exp e1
          | _ -> false)
    )
  | CP.Div (e1, e2, _) -> false
  | _ -> false

let is_linear_bformula b =
  let (pf,_) = b in
  match pf with
  | CP.BConst _ -> true
  | CP.BVar _ | CP.SubAnn _ -> true
  | CP.Lt (e1, e2, _) | CP.Lte (e1, e2, _)
  | CP.Gt (e1, e2, _) | CP.Gte (e1, e2, _)
  | CP.Eq (e1, e2, _) | CP.Neq (e1, e2, _) ->
    (is_linear_exp e1) && (is_linear_exp e2)
  | CP.EqMax (e1, e2, e3, _) | CP.EqMin (e1, e2, e3, _) ->
    (is_linear_exp e1) && (is_linear_exp e2) && (is_linear_exp e3)
  | _ -> false

let rec is_linear_formula f0 =
  match f0 with
  | CP.BForm (b,_) -> is_linear_bformula b
  | CP.AndList _ -> Gen.report_error no_pos "mathematica.ml: encountered AndList, should have been already handled"
  | CP.Not (f, _,_) | CP.Forall (_, f, _,_) | CP.Exists (_, f, _,_) ->
    is_linear_formula f;
  | CP.And (f1, f2, _) | CP.Or (f1, f2, _,_) ->
    (is_linear_formula f1) && (is_linear_formula f2)

let is_linear_formula f0 =
  Debug.no_1 "is_linear_formula" !print_formula string_of_bool is_linear_formula f0


let has_var_exp e0 =
  let f e =
    match e with
    | CP.Var _ -> Some true
    | _ -> None in
  CP.fold_exp e0 f or_list

let is_linear2 f0 =
  let f_bf bf =
    if CP.is_bag_bform bf || CP.is_list_bform bf then Some false
    else None in
  let rec f_e e = (
    if CP.is_bag e || CP.is_list e then Some false
    else
      match e with
      | CP.Mult (e1, e2, _) ->
        if (has_var_exp e1 && has_var_exp e2) then Some false
        else None
      | CP.Div (e1, e2, _) -> Some false
      | _ -> None
  ) in
  CP.fold_formula f0 (nonef, f_bf, f_e) and_list

(* LDK: not hold when using fractional permission *)
(* e1 < e2 ~> e1 <= e2 -1 *)
(* e1 > e2 ~> e1 >= e2 + 1 *)
(* e1 != e2 ~> e1 >= e2 + 1 or e1 <= e2 - 1  *)
let rec strengthen_formula f0 =
  match f0 with
  | CP.BForm ((pf,il),lbl) -> (
      match pf with
      | CP.Lt (e1, e2, l) -> CP.BForm ((CP.Lte (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l), il), lbl)
      | CP.Gt (e1, e2, l) -> CP.BForm ((CP.Gte (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l), il), lbl)
      | CP.Neq (e1, e2, l) ->
        let lp = CP.Lte (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l) in
        let rp = CP.Gte (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l) in
        CP.Or (CP.BForm ((lp,il), lbl), CP.BForm ((rp,il), lbl), lbl, l)
      | _ -> f0
    )
  | CP.Not (f, lbl, l) -> CP.Not (strengthen_formula f, lbl, l)
  | CP.Forall (sv, f, lbl, l) -> CP.Forall (sv, strengthen_formula f, lbl, l)
  | CP.Exists (sv, f, lbl, l) -> CP.Exists (sv, strengthen_formula f, lbl, l)
  | CP.And (f1, f2, l) -> CP.And (strengthen_formula f1, strengthen_formula f2, l)
  | CP.AndList _ -> Gen.report_error no_pos "mathematica.ml: encountered AndList, should have been already handled"
  | CP.Or (f1, f2, lbl, l) -> CP.Or (strengthen_formula f1, strengthen_formula f2, lbl, l)

let strengthen_formula f =
  let pr = string_of_formula in
  Debug.no_1 "strengthen_formula" pr pr strengthen_formula f

let strengthen2 f0 =
  let f_f f =
    match f with
    | CP.BForm ((CP.Neq (e1, e2, l), il), lbl) ->
      let lp = CP.Lte (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l) in
      let rp = CP.Gte (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l) in
      Some (CP.Or (CP.BForm ((lp, il), lbl), CP.BForm ((rp, il), lbl), lbl, l))
    | _ -> None in
  let f_bf bf =
    let (pf,il) = bf in
    match pf with
    | CP.Lt (e1, e2, l) -> Some ((CP.Lte (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l)),il)
    | CP.Gt (e1, e2, l) -> Some ((CP.Gte (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l)),il)
    | _ -> Some bf in
  CP.map_formula f0 (f_f, f_bf, nonef)

(* e1 <= e2 ~> e1 < e2 + 1 *)
(* e1 >= e2 ~> e1 > e2 - 1 *)
(* e1 = e2 ~> e2 - 1 < e1 < e2 + 1 *)
let rec weaken_formula f0 =
  match f0 with
  | CP.BForm ((pf,il),lbl) -> (
      match pf with
      | CP.Lte (e1, e2, l) -> CP.BForm ((CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l),l), il), lbl)
      | CP.Gte (e1, e2, l) -> CP.BForm ((CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l),l), il), lbl)
      | CP.Eq (e1, e2, l) ->
        let lp = CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l) in
        let rp = CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l) in
        CP.And (CP.BForm ((lp,il),lbl), CP.BForm ((rp,il),lbl), l)
      | _ -> f0
    )
  | CP.Not (f,lbl,l) -> CP.Not (weaken_formula f, lbl, l)
  | CP.Forall (sv, f, lbl, l) -> CP.Forall (sv, weaken_formula f, lbl, l)
  | CP.Exists (sv, f, lbl, l) -> CP.Exists (sv, weaken_formula f, lbl, l)
  | CP.And (f1, f2, l) -> CP.And (weaken_formula f1, weaken_formula f2, l)
  | CP.AndList _ -> Gen.report_error no_pos "mathematica.ml: encountered AndList, should have been already handled"
  | CP.Or (f1, f2, lbl, l) -> CP.Or (weaken_formula f1, weaken_formula f2, lbl, l)

let weaken2 f0 =
  let f_f f =
    match f with
    | CP.BForm ((CP.Eq (e1, e2, l),il), lbl) ->
      let lp = CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l) in
      let rp = CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l) in
      Some (CP.And (CP.BForm ((lp,il),lbl), CP.BForm ((rp,il),lbl), l))
    | _ -> None in
  let f_bf bf =
    let (pf,il) = bf in
    match pf with
    | CP.Lte (e1, e2, l) -> Some ((CP.Lt (e1, CP.Add(e2, CP.IConst (1, no_pos), l), l)),il)
    | CP.Gte (e1, e2, l) -> Some ((CP.Gt (e1, CP.Add(e2, CP.IConst (-1, no_pos), l), l)),il)
    | _ -> Some bf in
  CP.map_formula f0 (f_f, f_bf, nonef)

let negate_b_formula bf0 =
  let (pf,il) = bf0 in
  let npf = (
    match pf with
    | CP.BConst (b, pos) -> Some (CP.BConst (not b, pos))
    | CP.BVar (sv, pos) -> None
    | CP.Lt (e1, e2, pos) -> Some (CP.Gte (e1, e2, pos))
    | CP.Lte (e1, e2, pos) -> Some (CP.Gt (e1, e2, pos))
    | CP.Gt (e1, e2, pos) -> Some (CP.Lte (e1, e2, pos))
    | CP.Gte (e1, e2, pos) -> Some (CP.Lt (e1, e2, pos))
    | CP.Eq (e1, e2, pos) -> Some (CP.Neq (e1, e2, pos))
    | CP.Neq (e1, e2, pos) -> Some (CP.Eq (e1, e2, pos))
    | _ -> None
  ) in
  match npf with
  | None -> None
  | Some pf -> Some (pf,il)

let rec negate_formula f0 = match f0 with
  | CP.BForm (bf, lbl) -> (
      let neg_bf = negate_b_formula bf in
      match neg_bf with
      | Some new_bf -> CP.BForm (new_bf, lbl)
      | None -> CP.Not (CP.BForm (bf, lbl), None, no_pos)
    )
  | CP.And (f1, f2, pos) -> CP.Or (negate_formula f1, negate_formula f2, None, pos)
  | CP.AndList _ -> Gen.report_error no_pos "mathematica.ml: encountered AndList, should have been already handled"
  | CP.Or (f1, f2, lbl, pos) -> CP.And (negate_formula f1, negate_formula f2, pos)
  | CP.Not (f, lbl, pos) -> f
  | CP.Forall (sv, f, lbl, pos) -> CP.Exists (sv, negate_formula f, lbl, pos)
  | CP.Exists (sv, f, lbl, pos) -> CP.Forall (sv, negate_formula f, lbl, pos)

let negate_formula f0 =
  let pr = !print_formula in
  Debug.no_1 "negate_formula" pr pr negate_formula f0

let rec normalize_formula f0 =
  match f0 with
  | CP.BForm _ -> f0
  | CP.AndList _ -> Gen.report_error no_pos "mathematica.ml: encountered AndList, should have been already handled"
  | CP.And (f1, f2, pos) -> CP.And (normalize_formula f1, normalize_formula f2, pos)
  | CP.Or (f1, f2, lbl, pos) -> CP.Or (normalize_formula f1, normalize_formula f2, lbl, pos)
  | CP.Not (f1, lbl, pos) -> negate_formula f1
  | CP.Forall (sv, f, lbl, pos) -> CP.Forall (sv, normalize_formula f, lbl, pos)
  | CP.Exists (sv, f, lbl, pos) -> CP.Exists (sv, normalize_formula f, lbl, pos)

(**********************
   Verification works
 *********************)

let options_to_bool opts default =
  match opts with
  | Some opt -> (
      match opt with
      | Some v -> v
      | None -> default
    )
  | None -> default

let is_sat_no_cache_ops pr_w pr_s (f: CP.formula) (sat_no: string) : bool * float =
  if is_linear_formula f then
    call_omega (lazy (Omega.is_sat f sat_no))
  else (
    let f =
      if (!no_pseudo_ops || CP.is_float_formula f) then f
      else strengthen_formula f in
    let sf = math_of_formula pr_w pr_s f in
    let var_list = CP.fv f in
    let sv_list = List.map (fun v -> math_of_spec_var v) var_list in
    let fmath = (
      match sv_list with
      | [] -> sf
      | [sv] -> "Exists[" ^ sv ^ ", " ^ sf ^ "]"
      | _ ->
        let svar = "{" ^ (List.fold_left (fun s sv -> s ^ ", " ^ sv ) (List.hd sv_list) (List.tl sv_list)) ^ "}" in
        "Exists[" ^ svar ^ ", " ^ sf ^ "]"
    ) in
    let mathematica_input = "Reduce[" ^ fmath ^ ", Reals]\n" in
    let runner () = check_formula mathematica_input in
    let err_msg = "Timeout when checking #is_sat " ^ sat_no ^ "!" in
    let proc =  lazy (run_with_timeout runner err_msg) in
    let res, time = call_mathematica proc in
    let sat = options_to_bool (Some res) true in (* default is SAT *)
    (sat, time)
  )

let is_sat_no_cache_ops pr_w pr_s f sat_no =
  Debug.no_1 "is_sat_no_cache (mathematica)" !print_formula
    (fun (b,_) -> string_of_bool b)
    (fun _ -> is_sat_no_cache_ops pr_w pr_s f sat_no) f

let is_sat_ops_x pr_w pr_s f sat_no =
  fst(is_sat_no_cache_ops pr_w pr_s f sat_no)

let is_sat_ops pr_w pr_s f sat_no =
  Debug.no_2 "[mathematica] is_sat_ops" string_of_formula (fun c -> c) string_of_bool
    (fun f sat_no -> is_sat_ops_x pr_w pr_s f sat_no) f sat_no

let is_sat_x f sat_no =
  let (pr_w,pr_s) = CP.drop_complex_ops in
  is_sat_ops pr_w pr_s f sat_no

let is_sat f sat_no =
  Debug.no_2 "[mathematica] is_sat" string_of_formula (fun c -> c) string_of_bool is_sat_x f sat_no

let is_valid_ops pr_w pr_s f imp_no =
  let f = normalize_formula f in
  let sf = math_of_formula pr_w pr_s f in
  let var_list = CP.fv f in
  let sv_list = List.map (fun v -> math_of_spec_var v) var_list in
  let fmath = (
    match sv_list with
    | [] -> sf
    | [sv] -> "ForAll[" ^ sv ^ ", " ^ sf ^ "]"
    | _ ->
      let svar = "{" ^ (List.fold_left (fun s sv -> s ^ ", " ^ sv ) (List.hd sv_list) (List.tl sv_list)) ^ "}" in
      "ForAll[" ^ svar ^ ", " ^ sf ^ "]"
  ) in
  let mathematica_input = "Reduce[" ^ fmath ^ ", Reals]\n" in
  let runner () = check_formula mathematica_input in
  let err_msg = "Timeout when checking #imply " ^ imp_no ^ "!" in
  let proc = lazy (run_with_timeout runner err_msg) in
  let res, time = call_mathematica proc in
  let valid = options_to_bool (Some res) false in (* default is INVALID *)
  (valid, time)

let is_valid_ops pr_w pr_s f imp_no =
  Debug.no_2 "[mathematica] is_valid" string_of_formula (fun c -> c) (fun pair -> Gen.string_of_pair string_of_bool string_of_float pair)
    (fun _ _ -> is_valid_ops pr_w pr_s f imp_no) f imp_no

let imply_no_cache_ops pr_w pr_s (f : CP.formula) (imp_no: string) : bool * float =
  let res =
    if is_linear_formula f then
      call_omega (lazy (Omega.is_valid_with_default_ops pr_w pr_s f !timeout))
      (* (is_valid f imp_no) *)
    else
      let wf =
        if (!no_pseudo_ops || CP.is_float_formula f) then f
        else weaken_formula f in
      is_valid_ops pr_w pr_s wf imp_no in
  res

let imply_no_cache_ops pr_w pr_s (f : CP.formula) (imp_no: string) : bool * float =
  Debug.no_2 "[mathematica] imply_no_cache"
    (add_str "formula" string_of_formula)
    (add_str "imp_no" (fun c -> c)) (fun pair -> Gen.string_of_pair string_of_bool string_of_float pair)
    (fun _ _ -> imply_no_cache_ops pr_w pr_s f imp_no) f imp_no


let imply_ops pr_w pr_s ante conseq imp_no =
  let f = normalize_formula (CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos) in
  (*example of normalize: a => b <=> !a v b *)
  let sf = simplify_var_name f in
  let fstring = string_of_formula sf in
  log DEBUG ("\n#imply " ^ imp_no);
  log DEBUG ("ante: " ^ (string_of_formula ante));
  log DEBUG ("conseq: " ^ (string_of_formula conseq));
  let res =
    if !no_cache then fst (imply_no_cache_ops pr_w pr_s f imp_no)
    else
      try
        (*Be careful: incorrect fstring can result in errors because of caching*)
        let res = Hashtbl.find !impl_cache fstring in
        incr cached_count;
        log DEBUG "Cached.";
        res
      with Not_found -> (
          let res, time = imply_no_cache_ops pr_w pr_s f imp_no in
          let () = if time > cache_threshold then
              let () = log DEBUG "Caching."in
              Hashtbl.add !impl_cache fstring res in
          res
        ) in
  log DEBUG (if res then "VALID" else "INVALID");
  res

let imply_ops pr_w pr_s ante conseq imp_no =
  let pr = !CP.print_formula in
  Debug.no_2 "[mathematica.ml]imply_ops" pr pr string_of_bool
    (fun _ _ -> imply_ops pr_w pr_s ante conseq imp_no) ante conseq

let imply f imp_no =
  let (pr_w,pr_s) = CP.drop_complex_ops in
  imply_ops pr_w pr_s f imp_no

let imply ante conseq imp_no =
  Debug.no_3 "[mathematica] imply"
    (add_str "ante" string_of_formula)
    (add_str "conseq" string_of_formula)
    (add_str "imp_no" (fun c -> c))
    string_of_bool imply ante conseq imp_no

(* unimplemented *)
let simplify (f: CP.formula) : CP.formula =
  if is_linear_formula f then x_add_1 Omega.simplify f
  else f

let hull (f: CP.formula) : CP.formula =
  if is_linear_formula f then Omega.hull f
  else f

let pairwisecheck (f: CP.formula): CP.formula =
  if is_linear_formula f then x_add_1 Omega.pairwisecheck f
  else f
