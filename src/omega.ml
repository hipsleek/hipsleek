#include "xdebug.cppo"
(*
  Call Omega Calculator, send input to it
*)
open Globals
open GlobProver
open Gen.Basic
open Cpure
open VarGen

let set_generated_prover_input = ref (fun _ -> ())
let set_prover_original_output = ref (fun _ -> ())

let set_prover_type () = Others.last_tp_used # set Others.OmegaCalc

let set_proof_string str = Others.last_proof_string # set str
let set_proof_result str = Others.last_proof_result # set str

let omega_call_count: int ref = ref 0
let omega_call_count_for_infer: int ref = ref 0
let is_omega_running = ref false
let in_timeout = ref 10.0 (* default timeout is 15 seconds *)
let is_complex_form = ref false
let varLength = 48

(***********)
let test_number = ref 0
let last_test_number = ref 0
let log_all_flag = ref false
let omega_restart_interval = ref (-1)
let log_all = open_log_out ("allinput.oc" (* ^ (string_of_int (Unix.getpid ())) *) )

(* currently not used --should be removed*)
let infilename = ref (!tmp_files_path ^ "input.oc." ^ (string_of_int (Unix.getpid ())))
let resultfilename = ref (!tmp_files_path ^ "result.txt." ^ (string_of_int (Unix.getpid())))

(*let oc_maxVars = ref 1024*)
let print_pure = ref (fun (c:formula)-> "printing not initialized")

let print_exp = ref (fun (e: Cpure.exp) -> "printing not initialized")

let process = ref {name = "omega"; pid = 0;  inchannel = stdin; outchannel = stdout; errchannel = stdin}

let init_files () =
  begin
    infilename := "input.oc." ^ (string_of_int (Unix.getpid ()));
    resultfilename := "result.txt." ^ (string_of_int (Unix.getpid()));
  end

let omega_of_spec_var (sv : spec_var):string = match sv with
  | SpecVar (t, v, p) -> 
    let r = match (List.filter (fun (a,b,_)-> ((String.compare v b)==0) )!omega_subst_lst) with
      | []->
        (* omega doesn't allow variable name starting with underscore *)
        let v = if ((String.get v 0) == '_') then "v" ^ v 
          else v in
        let v =
          let reg = Str.regexp "\." in
          Str.global_replace reg "" v
        in
        let ln = (String.length v) in  
        let r_c = if (ln<20) then v
          else "v" ^ (String.sub v (ln-20)  20) in
        begin
          omega_subst_lst := (r_c,v,t)::!omega_subst_lst; 
          r_c end
      | (a,b,_)::h->  a in 
    r ^ (if is_primed sv then Oclexer.primed_str else "")


let rec omega_of_exp e0 = match e0 with
  | Null _ -> "0"
  | Var (SpecVar(_,n,_) as sv, _) -> 
    if n="null" then "0"
    else (omega_of_spec_var sv)
  | IConst (i, _) -> string_of_int i 
  | AConst (i, _) -> string_of_int(int_of_heap_ann i) 
  | Add (a1, a2, _) ->  (omega_of_exp a1)^ " + " ^(omega_of_exp a2) 
  | Subtract (a1, a2, _) ->  (omega_of_exp a1)^ " - " ^"("^(omega_of_exp a2)^")"
  | Mult (a1, a2, l) ->
        let r = match a1 with
          | IConst (i, _) -> (string_of_int i) ^ "(" ^ (omega_of_exp a2) ^ ")"
          | _ -> let rr = match a2 with
              | IConst (i, _) -> (string_of_int i) ^ "(" ^ (omega_of_exp a1) ^ ")"
              | _ -> 
                    (* "0=0" *)
                    illegal_format "[omega.ml] Non-linear arithmetic is not supported by Omega."
                    (* if (!Globals.non_linear_flag) then *)
                    (*   let () = report_warning no_pos "[omega.ml] Removing non-linear arithmetic expr." in *)
                    (*   (non_linear_detect # set ; "<non-linear>") *)
                    (* else *)
                    (*   Error.report_error { *)
                    (*       Error.error_loc = l; *)
                    (*       Error.error_text = "[omega.ml] Non-linear arithmetic is not supported by Omega." *)
                    (*   } *)
            in rr
        in r
  | Template t -> omega_of_exp (exp_of_template t)
  | Div (_, _, l) -> illegal_format "[omega.ml] Divide is not supported."
  (* Error.report_error { *)
  (*   Error.error_loc = l; *)
  (*   Error.error_text ="[omega.ml] Divide is not supported." *)
  (* } *)
  | Max _
  | Min _ -> illegal_format ("Omega.omega_of_exp: min/max should not appear here")
  | TypeCast (t, e1, p) -> omega_of_exp e1  (* illegal_format ("Omega.omega_of_exp: TypeCast should not appear here") *)
  | FConst _ -> illegal_format ("Omega.omega_of_exp: FConst")
  | Func _ -> "0" (* TODO: Need to handle *)
  | _ -> illegal_format ("Omega.omega_of_exp: array, bag or list constraint "^(!print_exp e0))
(*
(ArrayAt _|ListReverse _|ListAppend _|ListLength _|ListTail _|ListHead _|
ListCons _|List _|BagDiff _|BagIntersect _|BagUnion _|Bag _|FConst _)
*)

(* and omega_ptr_eq_null a1 = *)
(*   let v= omega_of_exp a1 in *)
(*   if !Globals.ptr_to_int_exact then ("("^v^" = 0)") *)
(*   else ("("^v^" < 1)") *)

(* and omega_ptr_neq_null a1 = *)
(*   let v= omega_of_exp a1 in *)
(*   if !Globals.ptr_to_int_exact then (v^" != 0") *)
(*   else (v^" > 0") *)

and omega_of_b_formula b =
  let (pf, _) = b in
  let aux pf =
    match pf with
      | Frm _ -> "(0=0)"
      | BConst (c, _) -> if c then "(1=1)" else "(0>0)"
      | XPure _ -> "(0=0)"
      | BVar (bv, _) ->  (omega_of_spec_var bv) ^ " > 0" (* easy to track boolean var *)
      | Lt (a1, a2, _) ->(omega_of_exp a1) ^ " < " ^ (omega_of_exp a2)
      | Lte (a1, a2, _) -> (omega_of_exp a1) ^ " <= " ^ (omega_of_exp a2)
      | Gt (a1, a2, _) ->  (omega_of_exp a1) ^ " > " ^ (omega_of_exp a2)
      | Gte (a1, a2, _) -> (omega_of_exp a1) ^ " >= " ^ (omega_of_exp a2)
      | SubAnn (a1, a2, _) -> (omega_of_exp a1) ^ " <= " ^ (omega_of_exp a2)
            (* | LexVar (_, a1, a2, _) -> "(0=0)" *)
      | Eq (a1, a2, _) -> begin
          (* if is_null a2 then *)
          (*   omega_ptr_eq_null a1 *)
          (*   (\* let v= omega_of_exp a1 in *\) *)
          (*   (\* if !Globals.ptr_to_int_exact then *\) *)
          (*   (\*   ("("^v^" < 1)") *\) *)
          (*   (\* else ("("^v^" = 0)") *\) *)
          (*   (\* ("("^v^" < 1 && "^v^" = xxxnull)") *\) *)
          (* else if is_null a1 then  *)
          (*   omega_ptr_eq_null a2 *)
          (*   (\* let v= omega_of_exp a2 in *\) *)
          (*   (\* ("("^v^" < 1)") *\) *)
          (*   (\* ("("^v^ " < 1 && "^v^" = xxxnull)") *\) *)
          (* else  *)
          (omega_of_exp a1) ^ " = " ^ (omega_of_exp a2)
        end
      | Neq (a1, a2, _) -> begin
          (* if is_null a2 then *)
          (*   omega_ptr_neq_null a1 *)
          (*       (\* (omega_of_exp a1) ^ " > 0" *\) *)
          (* else if is_null a1 then *)
          (*   omega_ptr_neq_null a2 *)
          (*   (\* (omega_of_exp a2) ^ " > 0" *\) *)
          (* else  *)
          (omega_of_exp a1)^ " != " ^ (omega_of_exp a2)
        end
      | EqMax (a1, a2, a3, _) ->
            let a1str = omega_of_exp a1 in
            let a2str = omega_of_exp a2 in
            let a3str = omega_of_exp a3 in
            "((" ^ a2str ^ " >= " ^ a3str ^ " & " ^ a1str ^ " = " ^ a2str ^ ") | ("
            ^ a3str ^ " > " ^ a2str ^ " & " ^ a1str ^ " = " ^ a3str ^ "))"
      | EqMin (a1, a2, a3, _) ->
            let a1str = omega_of_exp a1  in
            let a2str = omega_of_exp a2  in
            let a3str = omega_of_exp a3  in
            "((" ^ a2str ^ " >= " ^ a3str ^ " & " ^ a1str ^ " = " ^ a3str ^ ") | ("
            ^ a3str ^ " > " ^ a2str ^ " & " ^ a1str ^ " = " ^ a2str ^ "))"
                (* | VarPerm _ -> illegal_format ("Omega.omega_of_exp: VarPerm constraint") *)
      | RelForm _ -> 
            if !Globals.oc_weaken_rel_flag then "0=0"
            else illegal_format ("Omega.omega_of_exp: RelForm")
      | LexVar _ -> illegal_format ("Omega.omega_of_exp: LexVar 3")
      | _ -> illegal_format ("Omega.omega_of_exp: bag or list constraint")
  in 
  (* let () = non_linear_detect # reset in *)
  let ans = aux pf in
  (* let flag = non_linear_detect # get in *)
  (* let () = non_linear_detect # reset in *)
  (* if flag then "(0=0)" *)
  (* else *) ans
    
and omega_of_formula_x pr_w pr_s f  =
  let rec helper f =
    match f with
    | BForm ((b,_) as bf,_) ->
      begin
        match (pr_w b) with
        | None -> "(" ^ (omega_of_b_formula bf) ^ ")"
        | Some f -> helper f
      end
    | AndList _ ->
      begin
        let () = print_endline_quiet ("AndList:?"^(!print_formula f)) in
        report_error no_pos "omega.ml: encountered AndList, should have been already handled"
      end
    | And (p1, p2, _) -> "(" ^ (helper p1) ^ " & " ^ (helper p2 ) ^ ")"
    | Or (p1, p2,_ , _) -> let () = is_complex_form:= true in	"(" ^ (helper p1) ^ " | " ^ (helper p2) ^ ")"
    | Not (p,_ , _) ->       " (not (" ^ (omega_of_formula_x pr_s pr_w p) ^ ")) "
    | Forall (sv, p,_ , _) -> " (forall (" ^ (omega_of_spec_var sv) ^ ":" ^ (helper p) ^ ")) "
    | Exists (sv, p,_ , _) -> " (exists (" ^ (omega_of_spec_var sv) ^ ":" ^ (helper p) ^ ")) "
  in
  try
    helper f
  with _ as e ->
    let s = Printexc.to_string e in
      let () = x_dinfo_pp (* print_string_quiet *) ("Omega Error Exp:"^s^"\n Formula:"^(!print_formula f)^"\n") no_pos in
    (* let () = x_tinfo_hp (add_str "Omega Error format:" !print_formula) f in *)
    raise e

(* let omega_of_formula_x pr_w pr_s f = *)
(*   omega_of_formula_x pr_w pr_s (Trans_arr.translate_array_one_formula f) *)
(* ;; *)

let omega_of_formula i pr_w pr_s f  =
  let () = set_prover_type () in
  let pr = !print_formula in
  (*let () = print_string ("source:"^(string_of_int i)^": "^(pr f)^"\n"); flush_all in*)
  Debug.no_1_num i "omega_of_formula" 
    pr pr_id (fun _ -> omega_of_formula_x pr_w pr_s f) f

let omega_of_formula_old i f  =
  if has_template_formula f then None else
    let (pr_w, pr_s) = no_drop_ops in
    try 
      Some (omega_of_formula i pr_w pr_s f)
    with | _ ->
      None

let omega_of_formula_old i f  =
  let pr = !print_formula in
  Debug.no_1_num i "omega_of_formula_old"
    pr (pr_option pr_id) (fun _ -> omega_of_formula_old i f) f
let is_local_solver = ref (false: bool)


let omegacalc = if !compete_mode (* (Sys.file_exists "oc") *) then ref ("./oc":string)
  else ref ("oc":string)

let local_oc = "./oc"
let global_oc = try FileUtil.which "oc" with Not_found -> ""

let omegacalc = 
  if (Sys.file_exists local_oc) then ref local_oc
  else if (Sys.file_exists global_oc)  then ref global_oc
  else 
    begin
      print_endline "ERROR : oc cannot be found!!"; ref ("oc_cannot be found":string)
    end

(* let omegacalc = ref ("oc":string) *)
(*let modified_omegacalc = "/usr/local/bin/oc5"*)
(* TODO: fix oc path *)
(* let omegacalc = ref ("/home/locle/workspace/hg/cparser-1/sleekex/omega_modified/omega_calc/obj/oc": string) *)

let start_with str prefix =
  (String.length str >= String.length prefix) && (String.sub str 0 (String.length prefix) = prefix) 

let send_cmd cmd =
  if !is_omega_running then output_string (!process.outchannel) (cmd ^ "\n")

let set_process (proc: GlobProver.prover_process_t) = 
  process := proc

let prelude () =
  let finished = ref false in
  while not !finished do
    let line = input_line (!process.inchannel) in
    (*let () = print_endline line in *)
    (if !log_all_flag && (not !compete_mode) then
       output_string log_all ("[omega.ml]: >> " ^ line ^ "\nOC is running\n") );
    if (start_with line "#") then finished := true;
  done

(* start omega system in a separated process and load redlog package *)
let start_prover() =
  try (
    if not !is_omega_running then begin
      (* if (not !Globals.web_compile_flag) then  *)
      print_endline_quiet  ("\nStarting Omega..." ^ !omegacalc); flush stdout;
      last_test_number := !test_number;
      let () = Procutils.PrvComms.start !log_all_flag log_all ("omega", !omegacalc, [||]) set_process prelude in
      is_omega_running := true;
    end
  )
  with e -> (
      if (!compete_mode) then (
        print_endline "Unable to run the prover Omega!";
        print_endline "Please make sure its executable file (oc) is installed";
      );
      raise e
    )

(* stop Omega system *)
let stop () =
  if !is_omega_running then begin
    let num_tasks = !test_number - !last_test_number in
    if (not !Globals.web_compile_flag) then
      print_endline_quiet "";
      print_string_if !Globals.enable_count_stats ("Stop Omega... "^(string_of_int !omega_call_count)^" invocations ");
      print_string_if (!Globals.gen_baga_inv && !Globals.enable_count_stats) ("Infer: " ^ (string_of_int !omega_call_count_for_infer) ^ " invocations; Proving: " ^ (string_of_int (!omega_call_count - !omega_call_count_for_infer)) ^ " invocations");
      flush stdout;
    let () = Procutils.PrvComms.stop !log_all_flag log_all !process num_tasks Sys.sigkill (fun () -> ()) in
    is_omega_running := false;
  end

(* restart Omega system *)
let restart reason =
  if !is_omega_running then begin
    let () = print_string_if !Globals.enable_count_stats (reason^" Restarting Omega after ... "^(string_of_int !omega_call_count)^" invocations ") in
    Procutils.PrvComms.restart !log_all_flag log_all reason "omega" start_prover stop
  end
  else begin
    let () = print_string_if !Globals.enable_count_stats (reason^" not restarting Omega ... "^(string_of_int !omega_call_count)^" invocations ") in ()
  end

(*
  - in: input channel
  - out: receiving msg
  - Desc: read from the channel, return the msg
*)
let read_from_in_channel chn : string =
  let res = ref "" in
  let quitloop = ref false in
  while not !quitloop do
    let line = input_line chn in
    let n = String.length line in
    (* print_endline (line^"\n"); flush stdout; *)
    if n > 0 then begin
      (* print_string (line^"\n"); flush stdout; *)
      (if !log_all_flag then
         output_string log_all ("[omega.ml]: >> "^line^"\n") );
      if line.[0] != '#' then
        begin
          res := !res ^ line;
          if (line.[n-1] == '}') then
            quitloop := true;
        end;
    end;
  done;
  !res

(*
  - in: input channel
  - out: last non-comment line of the input channel
  - Desc: read from the channel, return the last line
*)	
let read_last_line_from_in_channel chn : string =
  let line = ref "" in
  let quitloop = ref false in
  while not !quitloop do
    line := (input_line chn);
    let n = String.length !line in
    if n > 0 then begin
      (* print_string (line^"\n"); flush stdout;*)
      (if !log_all_flag then 
         output_string log_all ("[omega.ml]: >> "^(!line)^"\n") );
      if !line.[0] != '#' then
        begin
          if(!line.[n-1] == '}') then
            quitloop := true;
        end;
    end;
  done;
  !line

(* let read_from_err_channel chn: bool= *)
(*   let line = input_line chn in *)
(*   if String.length line > 0 then *)
(*     let () = print_endline line in *)
(*     true *)
(*   else false *)

(* send formula to omega and receive result -true/false*)
let check_formula f timeout =
(*  try*)
  begin
    (* let () = x_binfo_pp f no_pos in *)
    if not !is_omega_running then start_prover ()
    else if (!omega_call_count = !omega_restart_interval) then
      begin
        restart("Regularly restart:1 ");
        omega_call_count := 0;
      end;
    let fnc f = 
      (* let () = print_endline ("check:" ^ f) in *)
      let () = incr omega_call_count in
      let new_f = Gen.break_lines_1024 f
      (*  if ((String.length f) > 1024) then
          	        (Gen.break_lines_1024 f)
          else
          	        f *)
      in
      output_string (!process.outchannel) new_f;
      flush (!process.outchannel);
      let result = ref true in
      let str = read_last_line_from_in_channel (!process.inchannel) in
      (* An Hoa : set original output *)
      let () = !set_prover_original_output str in
      let () = set_proof_result str in
      let n = String.length str in
      if n > 7 then
        begin
          let lastchars = String.sub str (n - 7) 7 in
          if lastchars = "FALSE }" then
            begin
              result := false;
            end;
        end;
      !result
    in
    let fail_with_timeout () = 
      restart ("[omega.ml]Timeout when checking sat for \n" ^ (string_of_float timeout));
      true (* it was checking for sat*) in
    if not (!dis_provers_timeout) then
      let res = Procutils.PrvComms.maybe_raise_and_catch_timeout_string_bool fnc f timeout fail_with_timeout in
      res
    else fnc f
  end

let check_formula f timeout =
  Gen.Profiling.do_2 "Omega:check_formula" check_formula f timeout

let check_formula i f timeout =
  Debug.no_2 "Omega:check_formula" (fun x->x) string_of_float string_of_bool
    check_formula f timeout

(* linear optimization with omega *)
let rec send_and_receive f timeout=
  begin
    if not !is_omega_running then
      start_prover (); 
    if (!omega_call_count = !omega_restart_interval) then
      begin
        restart ("Regularly restart:2");
        omega_call_count := 0;
      end;
    let fnc () =
      let () = incr omega_call_count in
      let new_f = Gen.break_lines_1024 f
      (*  if ((String.length f) > 1024) then
          (Gen.break_lines_1024 f)
          else
          f *)
      in
      let () = x_tinfo_hp (add_str "omega inp" idf) new_f no_pos in
      output_string (!process.outchannel) new_f;
      (* x_binfo_pp "after sending to omega" no_pos; *)
      flush (!process.outchannel);
      (* x_binfo_pp "after flushing to omega" no_pos; *)
      (* try *)
      let str = read_from_in_channel (!process.inchannel) in
      let () = x_tinfo_hp (add_str "omega out" idf) str no_pos in
      let () = set_proof_result str in
      let lex_buf = Lexing.from_string str in
      (*print_string (line^"\n"); flush stdout;*)
      let rel = Ocparser.oc_output (Oclexer.tokenizer "interactive") lex_buf in
      rel
      (* with e -> let () = read_from_err_channel (!process.errchannel) in *)
      (*           raise e *)
    in
    let answ = Procutils.PrvComms.maybe_raise_timeout_num 3 fnc () timeout in
    answ
  end

let send_and_receive f timeout =
  let pr x = x in
  let pr2 = Cpure.string_of_relation in
  Debug.no_2 "Omega:send_and_receive" pr string_of_float pr2 send_and_receive f timeout 

(********************************************************************)
let rec omega_of_var_list (vars : ident list) : string = match vars with
  | [] -> ""
  | [v] -> v
  | v :: rest -> v ^ ", " ^ (omega_of_var_list rest)

let get_vars_formula (p : formula):(string list) =
  let svars = fv p in
  (* let () = x_binfo_pp ("formula "^(!print_formula p)) no_pos in *)
  (* let () = x_binfo_pp ((pr_list string_of_spec_var) svars) no_pos in *)
  (*if List.length svars >= !oc_maxVars then (false, []) else*)
  List.map omega_of_spec_var svars

(*
  Use Omega Calculator to test if a formula is valid -- some other
  tool may probably be used ...
*)

let mkSpecVarList i svl =
  let svl1 = Cpure.remove_dups_svl svl in
  let r,fr,_ = List.fold_left (fun (r,fr,n) (Cpure.SpecVar(typ, id, p) as sv) ->
      if String.length id > varLength (* || String.compare (String.sub id 0 1) "_" == 0 *) then
        (r@[sv], fr@[(Cpure.SpecVar(typ, ("v" ^ string_of_int(n)), p))], n+1)
      else (r,fr,n)
    ) ([],[], i) svl1 in
  (r, fr )
(* if i == List.length svl then *)
(*   [] *)
(* else *)
(*   match List.nth svl i with *)
(*     | Cpure.SpecVar(typ, ident, primed) -> Cpure.SpecVar(typ, ("v" ^ string_of_int(i)), primed) :: mkSpecVarList (i + 1) svl *)

let is_sat_ops_x pr_weak pr_strong (pe : formula)  (sat_no : string): bool =
  (*print_endline (Gen.new_line_str^"#is_sat " ^ sat_no ^ Gen.new_line_str);*)
  incr test_number;
  (* print_string ("going omega-> "^(!print_formula pe)^"\n"); *)
  begin
    (*  Cvclite.write_CVCLite pe; *)
    (*  Lash.write pe; *)
    (* let pe0 = drop_varperm_formula pe in *)
    (* let pe = x_add_1 Cpure.subs_const_var_formula pe in *)
    let pe = if true (* !Globals.non_linear_flag *) then x_add_1 Cpure.drop_nonlinear_formula pe else pe in

    let pe = Trans_arr.translate_array_one_formula pe in
    let svl0 = Cpure.fv pe in
    let svl,fr_svl = mkSpecVarList 0 svl0 in
    let ss = List.combine svl fr_svl in
    let pe = Cpure.subst ss pe in
    let pvars = get_vars_formula pe in
    (*if not safe then true else*)
    begin
      omega_subst_lst := [];
      let vstr = omega_of_var_list (Gen.BList.remove_dups_eq (=) pvars) in
      (* let () = x_binfo_pp vstr no_pos in *)
      let fstr = omega_of_formula 1 pr_weak pr_strong pe in
      let fomega =  "{[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Gen.new_line_str in

      let () = set_proof_string ("SAT:"^fomega) in
      if !log_all_flag then begin
        output_string log_all (Gen.new_line_str^"#is_sat " ^ sat_no ^ Gen.new_line_str);
        output_string log_all (Gen.break_lines_1024 fomega);
        flush log_all;
      end;

      let sat =
        try
          check_formula 1 fomega (if !user_sat_timeout then !sat_timeout_limit else !in_timeout)
        with
        | Procutils.PrvComms.Timeout as exc ->
          let () = set_proof_result ("TIMEOUT") in
          if !Globals.dis_provers_timeout then (stop (); raise exc)
          else begin
            Printf.eprintf "SAT Unexpected exception : %s" (Printexc.to_string exc);
            stop (); raise exc end
        | End_of_file ->
          let () = set_proof_result ("END_OF_FILE") in
          (*let () = print_endline "SAT: End_of_file" in*)
          restart ("End_of_file when checking #SAT \n");
          true
        | exc ->
          begin
            let exs = Printexc.to_string exc in
            let () = set_proof_result ("EXCEPTION :"^exs) in
            Printf.eprintf "SAT Unexpected exception : %s" exs;
            stop (); raise exc
            (* restart ("Unexpected exception when doing IMPLY "); *)
            (* true *)
          end
      in
      (*   let post_time = Unix.gettimeofday () in *)
      (*   let time = (post_time -. pre_time) *. 1000. in *)

      if !log_all_flag = true then begin
        if sat then output_string log_all ("[omega.ml]: unsat "^sat_no ^(string_of_int !test_number)^" --> FAIL\n") else output_string log_all ("[omega.ml]: sat "^sat_no^(string_of_int !test_number)^" --> SUCCESS\n");
      end else ();
      sat
    end
  end

let is_sat_ops_x pw ps pe sat_no =
  try
    Wrapper.wrap_silence_output (is_sat_ops_x pw ps pe) sat_no
  with e ->
    begin
      if !Globals.oc_warning then
        let () = x_binfo_pp "WARNING: exception from Omega.is_sat_ops" no_pos in
        true
      else raise e;
    end


let is_sat_ops pr_weak pr_strong (pe : formula)  (sat_no : string): bool =
  Debug.no_1 "Omega.is_sat_ops" !print_formula (string_of_bool) (fun _ -> is_sat_ops_x pr_weak pr_strong pe sat_no) pe

let is_sat (pe : formula)  (sat_no : string): bool =
  let pr x = None in
  x_add_1 is_sat_ops pr pr pe sat_no

let is_sat (pe : formula)  (sat_no : string): bool =
  let pf = !print_pure in
  Debug.no_1 "Omega.is_sat" pf (string_of_bool) (fun _ -> is_sat pe sat_no) pe

let is_sat_weaken (pe : formula)  (sat_no : string): bool =
  let pe = drop_rel_formula pe in
  is_sat pe sat_no

let is_sat_with_check pr_weak pr_strong (pe : formula) sat_no : bool option =
  do_with_check "" (fun x -> is_sat_ops pr_weak pr_strong x sat_no) pe

let is_sat_with_check pr_weak pr_strong (pe : formula) sat_no : bool option =
  let pf = !print_pure in
  Debug.no_1 "Omega.is_sat_with_check" pf (pr_option string_of_bool) 
    (fun _ -> is_sat_with_check pr_weak pr_strong pe sat_no) pe

let is_sat_with_check_ops pr_weak pr_strong (pe : formula) sat_no : bool option =
  do_with_check "" (fun x -> is_sat_ops pr_weak pr_strong x sat_no) pe

let is_sat_with_check_ops pr_weak pr_strong (pe : formula) sat_no : bool option =
  let pf = !print_pure in
  Debug.no_1 "Omega.is_sat_with_check" pf (pr_option string_of_bool) 
    (fun _ -> is_sat_with_check_ops pr_weak pr_strong pe sat_no) pe

let is_sat (pe : formula) sat_no : bool =
  try
    is_sat pe sat_no
  with Illegal_Prover_Format s -> 
    begin
      print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :"^s);
      print_endline_quiet ("Apply Omega.is_sat on formula :"^(!print_pure pe));
      flush stdout;
      failwith s
    end

let is_valid_ops pr_weak pr_strong (pe : formula) timeout: bool =
  (*print_endline "LOCLE: is_valid";*)
  begin
    (* let pe0 = drop_varperm_formula pe in *)
    let pe = x_add_1 Cpure.subs_const_var_formula pe in
    let pe = if true (* !Globals.non_linear_flag *) then x_add_1 drop_nonlinear_formula_rev pe else pe in
    let svl0 = Cpure.fv pe in
    let svl,fr_svl = mkSpecVarList 0 svl0 in
    let ss = List.combine svl fr_svl in
    let pe = Cpure.subst ss pe in
    let pe = Trans_arr.translate_array_one_formula_for_validity pe in
    let pvars = get_vars_formula pe in
    (*if not safe then true else*)
    begin
      omega_subst_lst := [];
      let fstr = omega_of_formula 2 pr_strong pr_weak pe in
      let vstr = omega_of_var_list (Gen.BList.remove_dups_eq (=) pvars) in
      let fomega =  "complement {[" ^ vstr ^ "] : (" ^ fstr ^ ")}" ^ ";" ^ Gen.new_line_str in
      (*test*)
      (*print_endline (Gen.break_lines fomega);*)
      (* An Hoa : set generated input *)
      let () = !set_generated_prover_input fomega in
      let () = set_proof_string ("IMPLY:"^fomega) in
      if !log_all_flag then begin
        (*output_string log_all ("YYY" ^ (Cprinter.string_of_pure_formula pe) ^ "\n");*)
        output_string log_all (Gen.new_line_str^"#is_valid" ^Gen.new_line_str);
        output_string log_all (Gen.break_lines_1024 fomega);
        flush log_all;
      end;

      let sat =
        try
          not (check_formula 2 (fomega ^ "\n") !in_timeout)
        with
        | Procutils.PrvComms.Timeout as exc -> 
          let () = set_proof_result ("TIMEOUT") in
          if !Globals.dis_provers_timeout then (stop (); raise exc)
          else begin
            Printf.eprintf "IMPLY : Unexpected exception : %s" (Printexc.to_string exc);
            stop (); raise exc end
        | End_of_file ->
          let () = set_proof_result ("END_OF_FILE") in
          (*let () = print_endline "IMPLY: End_of_file" in*)
          (*let () = print_string ("\n"^fomega^"\n") in*)
          restart ("IMPLY : End_of_file when checking \n");
          false
        | exc ->
          begin
            let exs = Printexc.to_string exc in
            let () = set_proof_result ("EXCEPTION :"^exs) in
            Printf.eprintf "IMPLY : Unexpected exception : %s" exs;
            stop (); raise exc
            (* restart ("Unexpected exception when doing IMPLY "); *)
            (* false *)
          end
      in
      (*   let post_time = Unix.gettimeofday () in *)
      (*   let time = (post_time -. pre_time) *. 1000. in *)

      sat
    end
  end

let is_valid_ops p e pe tm =
  try
    Wrapper.wrap_silence_output (is_valid_ops p e pe) tm
  with e -> 
    begin
      if !Globals.oc_warning then
        let () = x_binfo_pp "WARNING: exception from Omega.is_valid" no_pos in
        false
      else raise e;
    end

(* let is_valid_ops pr_weak pr_strong (pe : formula) timeout: bool = *)
(* 	Debug.no_1 "Omega:is_valid_ops " !print_formula string_of_bool (fun _ -> is_valid_ops pr_weak pr_strong pe timeout) pe *)
(* (\* let is_valid (pe : formula) timeout: bool = *\) *)
(* (\*   let pr x = None in *\) *)
(* (\*   is_valid_ops pr pr pe timeout *\) *)

let is_valid_ops pr_weak pr_strong (pe : formula) timeout: bool =
  let pf = !print_pure in
  Debug.no_1 "Omega.is_valid" pf (string_of_bool) (fun _ -> is_valid_ops pr_weak pr_strong pe timeout) pe

let is_valid_with_check (pe : formula) timeout : bool option =
  do_with_check "" (fun x -> is_valid_ops (fun _ -> None) (fun _ -> None) x timeout) pe

(*let is_valid_with_check_ops pr_w pr_s (pe : formula) timeout : bool option =
  do_with_check "" (fun x -> is_valid_ops pr_w pr_s x timeout) pe*)

let is_valid_with_default_ops pr_w pr_s (pe : formula) timeout : bool = 
  do_with_check_default "" (fun x -> is_valid_ops pr_w pr_s x timeout) pe false


(* let is_valid (pe : formula) timeout : bool = *)
(*   do_with_check_default "Omega is_valid"  *)
(*       (fun x -> is_valid x timeout) pe false *)

let imply_ops pr_weak pr_strong (ante : formula) (conseq : formula) (imp_no : string) timeout : bool =
  (*print_endline "LOCLE: imply";*)
  incr test_number;
  (*
    let tmp1 = mkAnd ante (mkNot conseq no_pos) no_pos in
    let fvars = fv tmp1 in
    let tmp2 = mkExists fvars tmp1 no_pos in
    not (is_valid tmp2)
   *)

  (* let tmp_form = mkOr (mkNot_dumb ante None no_pos) conseq None no_pos in *)

  let tmp_form = mkOr (mkNot ante None no_pos) conseq None no_pos in

  let result = is_valid_ops pr_weak pr_strong tmp_form !in_timeout in
  if !log_all_flag = true then begin
    if result then 
      output_string log_all ("[omega.ml]: imp #" ^ imp_no ^ "-- test #" ^(string_of_int !test_number)^" --> SUCCESS\n") 
    else 
      output_string log_all ("[omega.ml]: imp "^imp_no^(string_of_int !test_number)^" --> FAIL\n");
  end else ();
  result

let imply_ops pr_weak pr_strong (ante : formula) (conseq : formula) (imp_no : string) timeout : bool =
  let pr = !print_formula in
  Debug.no_2 "omega.imply_ops_1" pr pr string_of_bool
    (fun _ _ -> imply_ops pr_weak pr_strong ante conseq imp_no timeout) ante conseq

let imply (ante : formula) (conseq : formula) (imp_no : string) timeout : bool =
  let (pr_w,pr_s) = drop_complex_ops in
  imply_ops pr_w pr_s (ante : formula) (conseq : formula) (imp_no : string) timeout 

let imply_with_check pr_weak pr_strong (ante : formula) (conseq : formula) (imp_no : string) timeout: bool option =
  do_with_check2 "" (fun a c -> imply_ops pr_weak pr_strong a c imp_no timeout) ante conseq

let imply_with_check_ops pr_weak pr_strong (ante : formula) (conseq : formula) (imp_no : string) timeout: bool option =
  do_with_check2 "" (fun a c -> imply_ops pr_weak pr_strong a c imp_no timeout) ante conseq

let imply_ops pr_weak pr_strong (ante : formula) (conseq : formula) (imp_no : string) timeout: bool =
  try
    imply_ops pr_weak pr_strong ante conseq imp_no timeout
  with Illegal_Prover_Format s -> 
    begin
      print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :"^s);
      print_endline_quiet ("Apply Omega.imply on ante Formula :"^(!print_pure ante));
      print_endline_quiet ("and conseq Formula :"^(!print_pure conseq));
      flush stdout;
      failwith s
    end

let imply_ops pr_weak pr_strong (ante : formula) (conseq : formula) (imp_no : string) timeout : bool =
  let pr = !print_formula in
  Debug.no_2 "[omega.ml]imply_ops_1" pr pr string_of_bool
    (fun _ _ -> imply_ops pr_weak pr_strong ante conseq imp_no timeout) ante conseq

let is_valid (pe : formula) timeout : bool =
  let (pr_w,pr_s) = drop_complex_ops in
  try
    is_valid_ops pr_w pr_s pe timeout
  with Illegal_Prover_Format s -> 
    begin
      print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :"^s);
      print_endline_quiet ("Apply Omega.is_valid on Formula :"^(!print_pure pe));
      flush stdout;
      failwith s
    end

let filter_imm_var_eq sv e f f_imm f_def =
  if is_True f (* && is_ann_typ sv  *)then 
    match e with
    | Var (ev, _) -> if (Str.string_match (Str.regexp "In_[0-9]*") (name_of_sv ev) 0 ) then f_imm else f_def
    | _ -> f_def
  else f_def

let is_valid (pe : formula) timeout : bool =
  Gen.Profiling.do_1 "omega.is_valid" is_valid pe timeout

let rec match_vars (vars_list0 : spec_var list) rel =
  (* let vars_list0 = vars_list0 in *)
  match rel with
  | ConstRel b ->
    if b then
      mkTrue no_pos
    else
      mkFalse no_pos
  | BaseRel (aelist0, f0) ->
    let rec match_helper vlist aelist f  = match aelist with
      | [] -> f
      | ae :: rest ->
        let v = List.hd vlist in
        let restvars = List.tl vlist in
        let restf = match_helper restvars rest f in
        let tmp1 = mkEqExp (Var (v, no_pos)) ae no_pos in
        let tmp2 = mkAnd_dumb tmp1 restf no_pos in
        let tmp2 = filter_imm_var_eq v ae f0 restf tmp2 in
        tmp2
    in
    if List.length aelist0 != List.length vars_list0 then
      begin
        Debug.info_zprint  (lazy  ("vlist:"^(!print_svl vars_list0)^" aelist:"^(pr_list !print_exp aelist0))) no_pos;
        illegal_format ("match_var: numbers of arguments do not match")
      end
    else
      match_helper vars_list0 aelist0 f0
  | UnionRel (r1, r2) ->
    let f1 = match_vars vars_list0 r1 in
    let f2 = match_vars vars_list0 r2 in
    let tmp = mkOr f1 f2 None no_pos in
    tmp

let match_vars (vars_list0 : spec_var list) rel =
  let pr = !print_svl in
  Debug.no_2 "match_vars" pr string_of_relation !print_formula (fun _ _ -> match_vars vars_list0 rel) vars_list0 rel

(* Made obselete as its *)
(* its functionality is now covered by norm_pure_result *)
(* let trans_bool (f: formula): formula = *)
(*   let get_bool_val is_lt e1 e2 pos = (\* e1 < e2 *\) *)
(*     let bv = get_boolean_var e1 in *)
(*     match bv with *)
(*     | Some v -> *)
(*       let i = get_num_int_opt e2 in *)
(*       begin match i with *)
(*         | Some i ->  *)
(*           let c = if is_lt then 1 else 0 in *)
(*           if i <= c then Some (mkNot (mkPure (BVar (v, pos))) None pos) (\* !v *\) *)
(*           else None *)
(*         | None -> None end *)
(*     | None ->   *)
(*       let bv = get_boolean_var e2 in *)
(*       match bv with *)
(*       | Some v -> *)
(*         let i = get_num_int_opt e1 in *)
(*         begin *)
(*           match i with *)
(*           | Some i -> *)
(*             let c = if is_lt then 0 else 1 in *)
(*             if i >= c then Some (mkPure (BVar (v, pos))) (\* v *\) *)
(*             else None *)
(*           | None -> None end *)
(*       | None -> None *)
(*   in  *)
(*   let f_f f = *)
(*     match f with *)
(*     | BForm (bf, _) -> *)
(*       let (pf, _) = bf in *)
(*       begin match pf with *)
(*         | Lt (e1, e2, pos) -> get_bool_val true e1 e2 pos *)
(*         | Lte (e1, e2, pos) -> get_bool_val false e1 e2 pos *)
(*         | Gt (e1, e2, pos) -> get_bool_val true e2 e1 pos *)
(*         | Gte (e1, e2, pos) -> get_bool_val false e2 e1 pos *)
(*         | _ -> Some f end *)
(*     | _ -> None *)
(*   in transform_formula (nonef, nonef, f_f, somef, somef) f *)

(* (==omega.ml#1156==) *)
(* Omega.trans_bool@559 *)
(* Omega.trans_bool inp1 : p=null & x=null & x'=null & res=v_boolean_64_1463' &  *)
(*  1<=v_boolean_64_1463' & 1<=v_bool_64_1477' *)
(* Omega.trans_bool@559 EXIT: p=null & x=null & x'=null & res=v_boolean_64_1463' & v_boolean_64_1463' &  *)
(*  v_bool_64_1477' *)
(* let trans_bool (f: formula): formula = *)
(*   let pr = !print_formula in *)
(*   Debug.no_1 "Omega.trans_bool" pr pr trans_bool f *)
let trans_bool (f: formula): formula = f

let simplify_ops_x pr_weak pr_strong (pe : formula) : formula =
  (* print_endline "LOCLE: simplify";*)
  (* let () = print_string ("\nomega_simplify: f
     before"^(!print_formula pe)) in *)
  let pe = Trans_arr.translate_array_one_formula pe in
  let () = x_tinfo_hp (add_str "simplify_ops_x(after trans_arr):" !print_formula) pe no_pos in
  begin
    let svl0 = Cpure.fv pe in	
    let svl,fr_svl = mkSpecVarList 0 svl0 in
    let ss1 = List.combine svl fr_svl in
    let ss2 = List.combine fr_svl svl in
    let pe1 =  Cpure.subst ss1 pe in
    (*let pe = drop_varperm_formula pe in*)
    let v = try 
        (* Debug.info_pprint "here1" no_pos; *)
        Some (omega_of_formula 8 pr_weak pr_strong pe1)
      with | Illegal_Prover_Format s ->
        (* Debug.info_pprint "here1a" no_pos; *)
        None
    in
    match v with
    | None -> (* Cpure.subst ss2 *) pe
    | Some fstr ->
      (* Debug.info_pprint "here2" no_pos;*) 
      omega_subst_lst := [];
      (* let vars_list = get_vars_formula pe1 in *)
      (*todo: should fix in code of OC: done*)
      (*if not safe then pe else*)
      begin
        try
          let sv_list = Gen.BList.remove_dups_eq Cpure.eq_spec_var (fv pe1) in
          (* let () = print_endline ("sv_list: " ^ (!Cpure.print_svl sv_list)) in *)
          let vstr = omega_of_var_list (List.map omega_of_spec_var sv_list) in
          let fomega =  "{[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Gen.new_line_str in
          (* x_binfo_hp (add_str "(simplify) input f" !print_formula) pe no_pos; *)
          (* x_binfo_hp (add_str "(simplify) fomega" pr_id) fomega no_pos;       *)
          (*test*)
          (*print_endline (Gen.break_lines fomega);*)
          (* for simplify/hull/pairwise *)
          let () = set_proof_string ("SIMPLIFY:"^fomega) in
          if !log_all_flag then begin
            (*                output_string log_all ("YYY" ^ (Cprinter.string_of_pure_formula pe) ^ "\n"); *)
            output_string log_all ("#simplify" ^ Gen.new_line_str ^ Gen.new_line_str);
            output_string log_all ((Gen.break_lines_1024 fomega) ^ Gen.new_line_str ^ Gen.new_line_str);
            flush log_all;
          end;
          let simp_f =
            try
              begin
                let timeo =
                  if (!is_complex_form) && String.length fomega > 1024 then
                    20.0
                  else !in_timeout
                in
                let rel = send_and_receive fomega timeo (* (!in_timeout) *) (* 0.0  *)in
                let () = is_complex_form := false in
                (* let () = print_endline ("after simplification: " ^ (Cpure.string_of_relation rel)) in *)
                let r = Cpure.subst ss2 (match_vars sv_list rel) in
                (* trans_bool *) r
              end
            with
            | Procutils.PrvComms.Timeout as exc ->
              (*log ERROR ("TIMEOUT");*)
              let () = set_proof_result ("TIMEOUT") in
              restart ("Timeout when checking #simplify ");
              if not (!Globals.dis_provers_timeout) then (* Cpure.subst ss2 *) pe
              else raise exc (* Timeout exception of a higher-level function *)
            | End_of_file ->
              let () = set_proof_result ("END_OF_FILE") in
              restart ("End_of_file when checking #simplify \n");
              (* Cpure.subst ss2 *) pe
            | exc -> (* stop (); raise exc  *)
              begin
                let exs = Printexc.to_string exc in
                let () = set_proof_result ("EXCEPTION :"^exs) in
                let () = print_endline_quiet ("WARNING (cannot simplify) : "^(!print_pure pe)) in
                let () = print_endline_quiet ("Exception : "^exs) in
                (* WN : 2 statements below disabled for TermInfer *)
                (* Printf.eprintf "Unexpected exception : %s" exs; *) 
                (* restart ("Unexpected exception when checking #simplify "^exs^"\n "); *)  
                (* Cpure.subst ss2 *) pe
              end
          in
          let () = is_complex_form := false in
          (*   let post_time = Unix.gettimeofday () in *)
          (*   let time = (post_time -. pre_time) *. 1000. in *)
          (*let () = print_string ("\nomega_simplify: f after"^(omega_of_formula simp_f)) in*)
          simp_f (* Cpure.subst ss2  simp_f *)
        with
        (* Timeout exception of provers is not expected at this level *)
        | Procutils.PrvComms.Timeout as exc -> let () = is_complex_form := false in raise exc 
        | _ -> let () = is_complex_form := false in
          (* Cpure.subst ss2 *) pe (* not simplified *)
      end
  end

let simplify_ops pr_weak pr_strong (pe : formula) : formula =
  let pf = !print_pure in
  Debug.no_1 "Omega.simplify_ops" pf pf 
    (fun _ -> simplify_ops_x pr_weak pr_strong pe) pe

let simplify (pe : formula) : formula =
  let pr_w, pr_s = 
    (* if !Globals.non_linear_flag then drop_nonlinear_formula_ops  *)
    (* else *) no_drop_ops in
  (* WN:todo - should not simplify with non-linear *)
  (* let pe =  *)
  (*   if !Globals.non_linear_flag then drop_nonlinear_formula_rev pe *)
  (*   else pe in *)
  (* simplify_ops pr_w pr_s pe *)
  let f_memo, subs, bvars = memoise_rel_formula [] pe in
  if has_template_formula f_memo then pe
  else
    (* let res_memo = simplify_ops pr_w pr_s f_memo in *)
    (* restore_memo_formula subs bvars res_memo *)
    try
      x_add simplify_ops pr_w pr_s pe
    with _ -> pe

let simplify (pe : formula) : formula =
  let pf = !print_pure in
  Debug.no_1 "Omega.simplify" pf pf (fun pe ->Trans_arr.translate_back_array_in_one_formula (simplify pe)) pe
;;

(* let simplify_ho is_complex (orig_pe : formula) : formula = *)
(*  (\* print_endline "LOCLE: simplify";*\) *)
(*   (\*let () = print_string ("\nomega_simplify: f before"^(omega_of_formula pe)) in*\) *)
(*   begin *)
(*     let (pe,subs,bvars) = memoise_formula_ho is_complex orig_pe in *)
(*     let (pr_weak,pr_strong) = no_drop_ops in *)
(*     let vars_list = get_vars_formula pe in *)
(*     (\*todo: should fix in code of OC: done*\) *)
(*     (\*if not safe then pe else*\) *)
(*     begin *)
(*       try *)
(*         omega_subst_lst := []; *)
(*         let fstr = omega_of_formula pr_weak pr_strong pe in *)
(*         let vstr = omega_of_var_list (Gen.BList.remove_dups_eq (=) vars_list) in *)
(*         let fomega =  "{[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Gen.new_line_str in *)
(* 	(\*test*\) *)
(* 	(\*print_endline (Gen.break_lines fomega);*\) *)
(*         if !log_all_flag then begin *)
(* (\*                output_string log_all ("YYY" ^ (Cprinter.string_of_pure_formula pe) ^ "\n");*\) *)
(*             output_string log_all ("#simplify" ^ Gen.new_line_str ^ Gen.new_line_str); *)
(*             output_string log_all ((Gen.break_lines_1024 fomega) ^ Gen.new_line_str ^ Gen.new_line_str); *)
(*             flush log_all; *)
(*         end; *)
(*         let simp_f = *)
(* 	      try *)
(*               begin *)
(* 	              let rel = send_and_receive fomega !in_timeout (\* 0.0  *\)in *)
(* 	              let new_pe = match_vars (fv pe) rel in *)
(*                   restore_memo_formula subs bvars new_pe  *)
(*                   (\* restore the extracted term and bool vars*\) *)
(* 	          end *)
(* 	      with *)
(*             | Procutils.PrvComms.Timeout -> *)
(*           (\*log ERROR ("TIMEOUT");*\) *)
(*                 restart ("Timeout when checking #simplify "); *)
(*                 orig_pe *)
(*             | End_of_file -> *)
(*                 restart ("End_of_file when checking #simplify \n"); *)
(*                 orig_pe *)
(*             | exc -> (\* stop (); raise exc  *\) *)
(*                 begin *)
(*                     Printf.eprintf "Unexpected exception : %s" (Printexc.to_string exc); *)
(*                     restart ("Unexpected exception when checking #simplify\n "); *)
(*                     orig_pe *)
(*                 end *)
(*         in *)
(*     (\*   let post_time = Unix.gettimeofday () in *\) *)
(*     (\*   let time = (post_time -. pre_time) *. 1000. in *\) *)
(*     (\*let () = print_string ("\nomega_simplify: f after"^(omega_of_formula simp_f)) in*\) *)
(*         simp_f *)
(*       with _ -> orig_pe (\* not simplified *\) *)
(*     end *)
(*   end *)

(* (\* does not work since complex term may be *)
(*    inside quantifers, subst may involve name capture *\) *)
(* let simplify_clever (pe : formula) : formula = *)
(*   let is_complex b = match b with *)
(*     | LexVar _  *)
(*     | RelForm _ -> true *)
(*     | _ -> false *)
(*   in simplify_ho is_complex pe *)

(* (\* let simplify_with_check (pe : formula) : formula option = *\) *)
(* (\*   do_with_check "Omega simplify" simplify pe *\) *)


(* let simplify_memo (pe : formula) : formula = *)
(*   match (do_with_check "" simplify_clever pe) *)
(*   with  *)
(*     | None -> pe *)
(*     | Some f -> f *)

(* let simplify_memo (pe : formula) : formula = *)
(*   let pf = !print_pure in *)
(*   Debug.no_1 "Omega.simplify_memo" pf pf simplify_memo pe *)

let simplify (pe : formula) : formula = if false (* not !Globals.oc_simplify *) then
    (* let () = print_endline ("OC.Simplify: " ^ (!print_pure pe) ) in *)
    pe
  else
    match (do_with_check "" simplify pe)
    with
    | None -> pe
    | Some f -> f

(* let wrap_ptr_to_int_exact = *)
(*   Wrapper.wrap_one_bool Globals.ptr_to_int_exact true *)

(* let simplify (pe : formula) : formula = *)
(*   let pr = !print_formula in *)
(*   Debug.no_1 "Omega.simplify" pr pr (wrap_ptr_to_int_exact simplify) pe  *)

let pairwisecheck2 (pe1 : formula) (pe2 : formula) : formula =
  begin
    omega_subst_lst := [];
    (* let pe1 = drop_varperm_formula pe1 in *)
    (* let pe2 = drop_varperm_formula pe2 in *)
    match ((omega_of_formula_old 21 pe1), (omega_of_formula_old 21 pe2)) with
    | (Some fstr1, Some fstr2) ->
      let vars_list1 = get_vars_formula pe1 in
      let vars_list2 = get_vars_formula pe2 in
      let vars_list = vars_list1@vars_list2 in
      let vstr = omega_of_var_list (Gen.BList.remove_dups_eq (=) vars_list) in
      let fomega =  "pairwisecheck ({[" ^ vstr ^ "] : (" ^ fstr1 ^ ")} union {[" ^ vstr ^ "] : (" ^ fstr2 ^ ")});" ^ Gen.new_line_str in
      let () = set_proof_string ("PAIRWISE:"^fomega) in
      (*test*)
      (*print_endline (Gen.break_lines fomega);*)
      if !log_all_flag then begin
        output_string log_all ("#pairwisecheck" ^ Gen.new_line_str ^ Gen.new_line_str);
        output_string log_all ((Gen.break_lines_1024 fomega) ^ Gen.new_line_str ^ Gen.new_line_str);
        flush log_all;
      end;
      let rel = send_and_receive fomega !in_timeout (* 0. *) in
      match_vars (remove_dups_svl ((fv pe1)@(fv pe2))) rel
    | _ -> Cpure.mkOr pe1 pe2 None no_pos
  end

let pairwisecheck (pe : formula) : formula =
  (* print_endline "LOCLE: pairwisecheck"; *)
  begin
    omega_subst_lst := [];
    (* let pe = drop_varperm_formula pe in *)


    match (omega_of_formula_old 21 pe) with
    | None -> pe
    | Some fstr ->
      try
        let vars_list = get_vars_formula pe in
        let vstr = omega_of_var_list (Gen.BList.remove_dups_eq (=) vars_list) in
        let fomega =  "pairwisecheck {[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Gen.new_line_str in
        let () = set_proof_string ("PAIRWISE:"^fomega) in
        (*test*)
        (*print_endline (Gen.break_lines fomega);*)
        if !log_all_flag then begin
          output_string log_all ("#pairwisecheck" ^ Gen.new_line_str ^ Gen.new_line_str);
          output_string log_all ((Gen.break_lines_1024 fomega) ^ Gen.new_line_str ^ Gen.new_line_str);
          flush log_all;
        end;
        let rel = send_and_receive fomega !in_timeout (* 0. *) in
      let r = match_vars (fv pe) rel in
      (* trans_bool *) r
      with 
      | End_of_file ->
          let () = set_proof_result ("END_OF_FILE") in
          restart ("PAIRWISECHECK: End_of_file exception occurs!\n");
          pe
      | exc -> raise exc
  end
;;

(* ZH *)
let pairwisecheck (pe:formula) : formula =
  (Trans_arr.translate_back_array_in_one_formula (pairwisecheck (x_add_1 Trans_arr.translate_array_one_formula pe)))
;;

let pairwisecheck (pe : formula) : formula =
  let r = pairwisecheck pe in
  if count_disj r > count_disj pe then pe
  else r

let wrap f = Wrapper.wrap_silence_output f

let pairwisecheck (pe : formula) : formula =
  let pf = !print_pure in
  Debug.no_1 "Omega.pairwisecheck" pf pf (Wrapper.wrap_silence_output pairwisecheck) pe

let hull (pe : formula) : formula =
  (*print_endline "LOCLE: hull";*)
  begin
    omega_subst_lst := [];
    (* let pe = drop_varperm_formula pe in *)
    match omega_of_formula_old 22 pe with
    | None -> pe
    | Some fstr ->
      let vars_list = get_vars_formula pe in
      let vstr = omega_of_var_list (Gen.BList.remove_dups_eq (=) vars_list) in
      let fomega =  "hull {[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Gen.new_line_str in
      let () = set_proof_string ("HULL:"^fomega) in

      (*test*)
      (*print_endline (Gen.break_lines fomega);*)

      if !log_all_flag then begin
        output_string log_all ("#hull" ^ Gen.new_line_str ^ Gen.new_line_str);
        output_string log_all ((Gen.break_lines_1024 fomega) ^ Gen.new_line_str ^ Gen.new_line_str);
        flush log_all;
      end;
      let rel = send_and_receive fomega !in_timeout (* 0. *) in
      match_vars (fv pe) rel
  end

let hull (pe : formula) : formula =
  let pf = !print_pure in
  Debug.no_1 "omega.hull" pf pf hull pe

let gist_x (pe1 : formula) (pe2 : formula) : formula =

  (*print_endline "LOCLE: gist";*)
  begin
    omega_subst_lst := [];
    (* let pe1 = drop_varperm_formula pe1 in *)
    let () = if no_andl pe1 && no_andl pe2 then () else report_warning no_pos "trying to do hull over labels!" in
    let fstr1 = omega_of_formula_old 23 pe1 in
    let fstr2 = omega_of_formula_old 24 pe2 in
    match fstr1,fstr2 with
    | Some fstr1, Some fstr2 ->
      begin
        let vars_list = remove_dups_svl (fv pe1 @ fv pe2) in
        let l1 = List.map omega_of_spec_var vars_list  in
        let vstr = String.concat "," l1  in
        let fomega =  "gist {[" ^ vstr ^ "] : (" ^ fstr1
                      ^ ")} given {[" ^ vstr ^ "] : (" ^ fstr2 ^ ")};" ^ Gen.new_line_str in
        (* gist not properly logged *)
        let () = x_tinfo_pp ("fomega = " ^ fomega) no_pos in
        let () = set_proof_string ("GIST(not properly logged yet):"^fomega) in
        if !log_all_flag then begin
          output_string log_all ("#gist" ^ Gen.new_line_str ^ Gen.new_line_str);
          output_string log_all ((Gen.break_lines_1024 fomega) ^ Gen.new_line_str ^ Gen.new_line_str);
          flush log_all;
        end;
        let rel = send_and_receive fomega !in_timeout (* 0.  *)in
        match_vars vars_list rel
      end
    | _, _ -> pe1
  end

let gist (pe1 : formula) (pe2 : formula) : formula =
  Debug.no_2 "gist" !print_formula !print_formula !print_formula gist_x pe1 pe2

let log_mark (mark : string) =
  if !log_all_flag then begin
    output_string log_all ("#mark: " ^ mark ^ Gen.new_line_str ^ Gen.new_line_str);
    flush log_all;
  end

let get_model bnd_vars assertions =
  let inp_f = mkExists bnd_vars (join_conjunctions assertions) None no_pos in
  simplify inp_f
