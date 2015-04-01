#include "xdebug.cppo"
open Share_prover
module PrvComms =
struct
  type proc = {name:string; pid: int; inchannel: in_channel; outchannel: out_channel; errchannel: in_channel }
  exception Timeout
  external set_close_on_exec : Unix.file_descr -> unit = "unix_set_close_on_exec";;
  let try_set_close_on_exec fd =
    try set_close_on_exec fd; true with Invalid_argument _ -> false
  let open_proc_full cmd args input output error toclose =
    let cloexec = List.for_all try_set_close_on_exec toclose in
    match Unix.fork() with
      0 -> Unix.dup2 input Unix.stdin; Unix.close input;
      Unix.dup2 output Unix.stdout; Unix.close output;
      Unix.dup2 error Unix.stderr; Unix.close error;
      if not cloexec then List.iter Unix.close toclose;
      begin try Unix.execvp cmd args
        with _ -> exit 127
      end
    | id -> id
  let open_process_full cmd args =
    let (in_read, in_write) = Unix.pipe() in
    let (out_read, out_write) = Unix.pipe() in
    let (err_read, err_write) = Unix.pipe() in
    let inchan = Unix.in_channel_of_descr in_read in
    let outchan = Unix.out_channel_of_descr out_write in
    let errchan = Unix.in_channel_of_descr err_read in
    let id = open_proc_full cmd args out_read in_write err_write [in_read; out_write; err_read] in
    Unix.close out_read;
    Unix.close in_write;
    Unix.close err_write;
    (inchan, outchan, errchan, id)
  let open_proc cmd args out_file:int  =
    match Unix.fork() with
    |  0 -> begin
        let output = Unix.openfile out_file [Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
        Unix.dup2 output Unix.stdout; Unix.close output;
        try Unix.execvp cmd args with _ -> exit 127 end
    | id -> id
  let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout)
  let set_timer tsecs = ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = tsecs })
  (* same as maybe_raise_timoeut just that it treats the timeout exception with the with_timeout function *)
  let maybe_raise_and_catch_timeout (fnc: 'a -> 'b) (arg: 'a) (tsec: float) (with_timeout: unit -> 'b): 'b =
    try
      let old_handler = Sys.signal Sys.sigalrm sigalrm_handler in
      let reset_sigalrm () = Sys.set_signal Sys.sigalrm old_handler in
      let () = set_timer tsec in
      let answ = fnc arg in
      set_timer 0.0;
      reset_sigalrm ();
      answ
    with
    | Timeout ->
      Printf.eprintf " maybe_raise_and_catch_timeout : UNEXPECTED Timeout after %s secs" (string_of_float tsec);
      (with_timeout ())
    | exc -> begin
        Printf.eprintf " maybe_raise_and_catch_timeout : Unexpected exception : %s" (Printexc.to_string exc);
        raise exc
      end
  (* closes the pipes of the named process *)
  let close_pipes (process: proc) : unit =
    (try
       flush process.outchannel;
       Unix.close (Unix.descr_of_out_channel process.outchannel);
       Unix.close (Unix.descr_of_in_channel process.errchannel)
     with | e -> () );
    (try
       Unix.close (Unix.descr_of_in_channel process.inchannel)
     with | e -> () )
  let start (prover: string * string * string array) set_process =
    let (prover_name, prover_proc, prover_arg_array) = prover in
    try
      let inchn, outchn, errchn, npid = open_process_full prover_proc prover_arg_array in
      let process = {name = prover_name; pid = npid; inchannel = inchn; outchannel = outchn; errchannel = errchn} in
      set_process process
    with
    | e -> begin
        let () = print_string ("\n["^prover_name^".ml ]Unexpected exception while starting prover "^ prover_name ^ "\n") in
        flush stdout; flush stderr;
        raise e
      end
  let stop (process:proc) (invocations: int) (killing_signal: int) =
    close_pipes process;
    try
      Unix.kill process.pid killing_signal;
      ignore (Unix.waitpid [] process.pid)
    with
    | e ->  ()
  let restart start stop = stop ();  start ()
(* to delete *)
(* module Ss_Z3:SAT_SLV = functor (Sv:SV) -> *)
(* struct *)
(*   type t_var = Sv.t *)
(*   type nz_cons = t_var list list *)
(*   type p_var = (\*include Gen.EQ_TYPE with type t=v*\) *)
(*     | PVar of t_var *)
(*     | C_top *)
(*   type eq_syst = (t_var*t_var*p_var) list *)
(*   let stringofTvar = Sv.string_of *)
(*   let stringofPvar v = match v with | C_top -> "T" | PVar v -> Sv.string_of v *)
(*   let mkTop () = C_top *)
(*   let mkVar v = PVar v *)
(*   let getVar v = match v with | C_top -> None | PVar v -> Some v *)
(*   let string_of_eq (v1,v2,v3) = (Sv.string_of v1)^" * "^(Sv.string_of v2)^" = "^(match v3 with | PVar v3 ->  Sv.string_of v3 | _ -> " true") *)
(*   let string_of_eq_l l = String.concat "\n" (List.map string_of_eq l) *)
(*   (\**********Z3 interface **********\) *)
(*   (\** Create a boolean variable using the given name. *\) *)
(*   let mk_bool_var ctx name = Z3.mk_const ctx (Z3.mk_string_symbol ctx name) (Z3.mk_bool_sort ctx) *)
(*   let mk_sv_bool_var ctx sv  =  mk_bool_var ctx (Sv.get_name sv) *)
(*   (\** Create a logical context.  Enable model construction. Also enable tracing to stderr. *\) *)
(*   let mk_context ()= *)
(*     let cfg = Z3.mk_config () in *)
(*     Z3.set_param_value cfg "MODEL" "false" ; *)
(*     let ctx = Z3.mk_context cfg in *)
(*     Z3.trace_to_stderr ctx; *)
(*     ctx *)
(*   (\** Check if  ctx is sat. if sat, then could get the model.*\) *)
(*   let check ctx =(match Z3.check ctx with *)
(*       | Z3.L_FALSE -> false *)
(*       | Z3.L_UNDEF ->  print_string "unknown\n"; failwith "unknown sat" *)
(*       | Z3.L_TRUE -> true ) *)
(*   let add_eqs ctx = *)
(*     List.iter (fun (v1,v2,v3)-> *)
(*         let bv1 = mk_sv_bool_var ctx v1 in *)
(*         let bv2 = mk_sv_bool_var ctx v2 in *)
(*         let xor12 = Z3.mk_xor ctx bv1 bv2 in *)
(*         match v3 with *)
(*         | PVar v3-> *)
(*           (Z3.assert_cnstr ctx (Z3.mk_not ctx (Z3.mk_and ctx [|bv1;bv2|])); *)
(*            Z3.assert_cnstr ctx (Z3.mk_eq ctx xor12 (mk_sv_bool_var ctx v3))) *)
(*         | C_top  -> Z3.assert_cnstr ctx xor12 *)
(*       ) *)
(*   let add_one_nz ctx l= Z3.assert_cnstr ctx (Z3.mk_or ctx (Array.of_list (List.map (mk_sv_bool_var ctx) l))) *)
(*   let add_nz ctx = List.iter (add_one_nz ctx) *)
(*   let check_sat_nz ctx non_zeros = *)
(*     Z3.push ctx; *)
(*     add_nz ctx non_zeros; *)
(*     if  check ctx then (Z3.pop ctx 1;true) *)
(*     else *)
(*       (Z3.pop ctx 1; *)
(*        List.for_all (fun l -> *)
(*            Z3.push ctx; *)
(*            add_one_nz ctx l; *)
(*            let r= check ctx in *)
(*            Z3.pop ctx 1; *)
(*            r) non_zeros ) *)
(*   let call_sat non_zeros eqs = *)
(*     let ctx = mk_context () in *)
(*     add_eqs ctx eqs; *)
(*     let r = check_sat_nz ctx non_zeros in *)
(*     Z3.del_context ctx; r *)
(*   let call_sat non_zeros eqs = *)
(*     let nzs = String.concat "," (List.map (fun l-> "{"^(String.concat "," (List.map Sv.string_of l))^"}") non_zeros) in *)
(*     let eqss = string_of_eq_l eqs in *)
(*     print_string ("Z3 SAT: "^nzs^"\n"^eqss^"\n"); *)
(*     let r = call_sat non_zeros eqs in *)
(*     print_string ("r: "^(string_of_bool r)^"\n"); r *)
(*   let call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars  = *)
(*     let ctx = mk_context () in *)
(*     add_eqs ctx a_l_eqs; *)
(*     print_string "added eqs\n";flush_all (); *)
(*     if not (check_sat_nz ctx a_nz_cons) then (Z3.del_context ctx;true) *)
(*     else *)
(*       let tbl = Hashtbl.create 20 in *)
(*       let bool_sort = Z3.mk_bool_sort ctx in *)
(*       let () = List.fold_left (fun c v-> Hashtbl.add tbl (Sv.get_name v) (Z3.mk_bound ctx c bool_sort); c+1) 1 c_ev in *)
(*       print_string "added exists\n";flush_all (); *)
(*       let mk_sv_bool_var_ex v = *)
(*         let nm = Sv.get_name v in *)
(*         try *)
(*           Hashtbl.find tbl nm *)
(*         with Not_found -> mk_bool_var ctx nm in *)
(*       let conseq = *)
(*         let f_ccv = List.fold_left (fun a (v,c)-> *)
(*             let z3v = mk_sv_bool_var_ex v in *)
(*             let z3v = if c then z3v else Z3.mk_not ctx z3v  in *)
(*             Z3.mk_and ctx [| a ; z3v|] *)
(*           ) (Z3.mk_true ctx) c_const_vars in *)
(*         let f_sv = List.fold_left (fun a (v1,v2)-> *)
(*             let z3v1 = mk_sv_bool_var_ex v1 in *)
(*             let z3v2 = mk_sv_bool_var_ex v2 in *)
(*             let z3eq = Z3.mk_eq ctx z3v1 z3v2 in *)
(*             Z3.mk_and ctx [|a; z3eq|] *)
(*           ) f_ccv c_subst_vars in *)
(*         let f_nz = List.fold_left (fun a l -> *)
(*             let nz_arr = Array.of_list (List.map mk_sv_bool_var_ex l) in *)
(*             Z3.mk_and ctx [|a;Z3.mk_or ctx nz_arr|] *)
(*           ) f_sv c_nz_cons in *)
(*         let f_eqs = List.fold_left (fun a (v1,v2,v3)-> *)
(*             let z3v1 = mk_sv_bool_var_ex v1 in *)
(*             let z3v2 = mk_sv_bool_var_ex v2 in *)
(*             let xor12 = Z3.mk_xor ctx z3v1 z3v2 in *)
(*             let f1 = Z3.mk_not ctx (Z3.mk_and ctx [|z3v1;z3v2|]) in *)
(*             let a  = Z3.mk_and ctx [|a;f1|] in *)
(*             match v3 with *)
(*             | PVar v3 -> Z3.mk_and ctx [| a;  Z3.mk_eq ctx xor12 (mk_sv_bool_var_ex v3) |] *)
(*             | C_top -> Z3.mk_and ctx [| a;  xor12 |] *)
(*           ) f_nz c_l_eqs in *)
(*         let l = List.length c_ev in *)
(*         let types = Array.init l (fun _ -> bool_sort) in *)
(*         let names = Array.init l (Z3.mk_int_symbol ctx) in *)
(*         Z3.mk_forall ctx 0 [||] types names f_eqs in *)
(*       print_string "constructed conseq\n";flush_all (); *)
(*       Z3.assert_cnstr ctx (Z3.mk_not ctx conseq); *)
(*       print_string "added conseq\n";flush_all (); *)
(*       let r = Z3.check ctx in *)
(*       print_string "actuall check\n";flush_all (); *)
(*       Z3.del_context ctx; *)
(*       match r with *)
(*       | Z3.L_FALSE ->	true *)
(*       | Z3.L_UNDEF ->	print_string "unknown\n"; false *)
(*       | Z3.L_TRUE  ->	false *)
(*   let call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars  = *)
(*     let nzs = *)
(*       String.concat "," ( *)
(*         List.map (fun l-> "{"^(String.concat "," (List.map Sv.string_of l))^"}") a_nz_cons) in *)
(*     let eqss = string_of_eq_l a_l_eqs in *)
(*     print_string ("\n Imply: "^nzs^"\n"^eqss^"\n");flush_all (); *)
(*     let r = call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars in *)
(*     print_string ("r: "^(string_of_bool r)); r *)
(* end;; *)
(* to delete *)
(************************************************************************************)
module Ss_Z3_proc:SAT_SLV = functor (Sv:SV) ->
struct
  type t_var = Sv.t
  type nz_cons = t_var list list
  type p_var = (*include Gen.EQ_TYPE with type t=v*)
    | PVar of t_var
    | C_top
  type eq_syst = (t_var*t_var*p_var) list
  let stringofTvar = Sv.string_of
  let stringofPvar v = match v with | C_top -> "T" | PVar v -> Sv.string_of v
  let mkTop () = C_top
  let mkVar v = PVar v
  let getVar v = match v with | C_top -> None | PVar v -> Some v
  let string_of_eq (v1,v2,v3) = (Sv.string_of v1)^" * "^(Sv.string_of v2)^" = "^(match v3 with | PVar v3 ->  Sv.string_of v3 | _ -> " true")
  let string_of_eq_l l = String.concat "\n" (List.map string_of_eq l)
  (**********Z3 interface **********)
  (**********Z3 interface **********)
  (**********Z3 interface **********)
  (**********Z3 interface **********)
  let smt_of_acons (v,c) = if c then Sv.string_of v else "(not " ^(Sv.string_of v) ^" )"
  let smt_of_asub (v1,v2) = "(= " ^(Sv.string_of v1) ^ " " ^ (Sv.string_of v2) ^ ")"
  let smt_of_eq (v1,v2,v3) =
    (*"(= " ^ "(and " ^(Sv.string_of v1)^ " " ^ (Sv.string_of v2)^")" ^ " " ^ (match v3 with PVar v-> Sv.string_of v | _ -> "1") ^ ")"*)
    let xor12 = "(xor " ^(Sv.string_of v1)^ " " ^ (Sv.string_of v2)^")" in
    match v3 with
    | PVar v3->
      let eq = "(= " ^ xor12 ^ " " ^ (Sv.string_of v3) ^ ")" in
      let neq = "(not (and " ^ (Sv.string_of v1)^ " " ^ (Sv.string_of v2) ^ " ) )" in
      "(and " ^ eq^ " " ^ neq ^ " )"
    | C_top  -> xor12
  let smt_of_anz nz = match nz with
    | [] -> failwith "error, unexpected empty nz"
    | h::t -> List.fold_left (fun a c-> "(or " ^ a ^ " " ^ (Sv.string_of c) ^ ")") (Sv.string_of h) t
  let smt_of_ante (_,anz,asub,acons,aeq) =
    let acons = List.map (fun c-> "(assert " ^ (smt_of_acons c) ^ ")\n") acons in
    let asub = List.map (fun c-> "(assert " ^ (smt_of_asub c) ^ ")\n") asub in
    let aeq = List.map (fun c-> "(assert " ^ (smt_of_eq c) ^ ")\n") aeq in
    let anz = List.map (fun c-> "(assert " ^ (smt_of_anz c) ^ ")\n") anz in
    String.concat "" (acons@asub@aeq@anz)
  let smt_of_conseq (cex,cnz,csub,ccons,ceq) =
    let ccons = List.map smt_of_acons ccons in
    let csub = List.map smt_of_asub csub in
    let ceq = List.map smt_of_eq ceq in
    let cnz = List.map smt_of_anz cnz in
    let s = List.fold_left (fun a c-> "(and " ^ a ^ " " ^ c ^ ")") "true" (ccons@csub@ceq@cnz) in
    List.fold_left (fun a c -> "(exists ((" ^ (Sv.string_of c) ^ " Bool)) " ^ a ^ ")") s cex
  (***************************************************************
     INTERATION
   **************************************************************)
  type sat_type =
    | Sat		(* solver returns sat *)
    | UnSat		(* solver returns unsat *)
    | Unknown	(* solver returns unknown or there is an exception *)
    | Aborted (* solver returns an exception *)
  (* Collect all Z3's output into a list of strings *)
  let rec icollect_output chn accumulated_output : string list =
    let output = try
        let line = input_line chn in
        if ((String.length line) > 7) then (*something diff to sat/unsat/unknown, retry-may lead to timeout here*)
          icollect_output chn (accumulated_output @ [line])
        else accumulated_output @ [line]
      with
      | End_of_file -> accumulated_output in
    output
  let sat_type_from_string r input=
    if (r = "sat") then Sat
    else if (r = "unsat") then UnSat
    else
      try
        let (todo_unk:int) = Str.search_forward (Str.regexp "unexpected") r 0 in
        (print_string "Z3 translation failure!"; failwith ("Z3 translation failure!!\n"^r^"\n input: "^input))
      with
      | Not_found -> Unknown
  let iget_answer chn input=
    let output = icollect_output chn [] in
    sat_type_from_string (List.nth output (List.length output - 1)) input
  let remove_file filename = try Sys.remove filename with | e -> ()
  (* Global settings *)
  let prover_process = ref {
      PrvComms.name = "z3";
      PrvComms.pid = 0;
      PrvComms.inchannel = stdin;
      PrvComms.outchannel = stdout;
      PrvComms.errchannel = stdin
    }
  let smtsolver_name = ref ("z3": string)
  let z3_call_count: int ref = ref 0
  let is_z3_running = ref false
  (***********)
  let test_number = ref 0
  let last_test_number = ref 0
  let z3_restart_interval = ref (-1)
  let path_to_z3 = "z3" (*"z3"*)
  let smtsolver_name = ref ("z3": string)
  (* start z3 system in a separated process and load redlog package *)
  and start() =
    if not !is_z3_running then begin
      print_string "Starting z3... \n"; flush stdout;
      last_test_number := !test_number;
      PrvComms.start (!smtsolver_name, !smtsolver_name, [|!smtsolver_name;"-smt2"; "-si"|]) (fun proc ->  prover_process := proc);
      is_z3_running := true;
    end
  (* stop Z3 system *)
  let stop () =
    if !is_z3_running then begin
      let num_tasks = !test_number - !last_test_number in
      print_string ("Stop z3... "^(string_of_int !z3_call_count)^" invocations "); flush stdout;
      let () = PrvComms.stop !prover_process num_tasks Sys.sigkill in
      is_z3_running := false;
    end
  (* restart Z3 system *)
  let restart reason =
    if !is_z3_running then
      let () = print_string (reason^" Restarting z3 after ... "^(string_of_int !z3_call_count)^" invocations ") in
      PrvComms.restart start stop
    else print_string (reason^" not restarting z3 ... "^(string_of_int !z3_call_count)^" invocations ")
  (* send formula to z3 and receive result -true/false/unknown*)
  let check_formula f timeout =
    begin
      if not !is_z3_running then start ()
      else if (!z3_call_count = !z3_restart_interval) then
        begin
          restart("Regularly restart:1 ");
          z3_call_count := 0;
        end;
      let fnc f =
        incr z3_call_count;
        output_string (!prover_process.PrvComms.outchannel) ("(push)\n" ^ f ^ "(pop)\n");
        flush (!prover_process.PrvComms.outchannel);
        iget_answer (!prover_process.PrvComms.inchannel) f
      in
      let fail_with_timeout () = restart ("[z3.ml]Timeout when checking sat!" ^ (string_of_float timeout)); Unknown in
      PrvComms.maybe_raise_and_catch_timeout fnc f timeout fail_with_timeout
    end
  let rec rem_dups l = match l with [] -> [] | q::qs -> if (List.exists (Sv.eq q) qs) then rem_dups qs else q::(rem_dups qs)
  let fv (exv,nz,subs,cons,eqs)=
    let w1,w2 = List.split subs in
    let fv_eq (v1,v2,v3)= v1::v2::(match v3 with C_top -> [] | PVar v-> [v]) in
    exv@(List.concat nz)@(fst (List.split cons))@w1@w2@(List.concat (List.map fv_eq eqs))
  let to_smt  ante conseq : string =
    let conseq1 = match conseq with
      | None -> ([],[],[],[],[])
      | Some f -> f in
    let all_fv = rem_dups (fv ante @ fv conseq1) in
    let smt_var_decls = String.concat "" (List.map (fun v -> "(declare-fun " ^ (Sv.string_of v) ^ " () Bool)\n" ) all_fv) in
    let ante_str = smt_of_ante ante in
    let conseq_str = if conseq=None then "false" else smt_of_conseq conseq1 in
    ( ";Variables declarations\n" ^smt_var_decls ^ ";Antecedent\n" ^  ante_str ^ ";Negation of Consequence\n" ^ "(assert (not " ^ conseq_str ^ "))\n" ^ "(check-sat)")
  let call_imply (a_ev:t_var list) (a_nz_cons:nz_cons) (a_l_eqs:eq_syst) (c_ev:t_var list) (c_nz_cons:nz_cons) (c_l_eqs:eq_syst)
      (c_const_vars:(t_var*bool) list) (c_subst_vars:(t_var*t_var) list):bool  =
    let input = to_smt (a_ev, a_nz_cons, [],[],a_l_eqs) (Some (c_ev, c_nz_cons, c_subst_vars, c_const_vars, c_l_eqs)) in
    (*print_string ("\n \n z3 input: "^(input)^"\n");*)
    match check_formula input 0. with
    | Sat -> false
    | UnSat -> true
    | Unknown -> false
    | Aborted -> false
  let call_sat non_zeros eqs =
    match (check_formula (to_smt ([],non_zeros,[],[],eqs) None)) 10.0 with
    | UnSat -> false
    | _ -> true
  let call_sat non_zeros eqs =
    let nzs = String.concat "," (List.map (fun l-> "{"^(String.concat "," (List.map Sv.string_of l))^"}") non_zeros) in
    let eqss = string_of_eq_l eqs in
    (*print_string ("Z3 SAT: "^nzs^"\n"^eqss^"\n");*)
    let r = call_sat non_zeros eqs in
    (*print_string ("r: "^(string_of_bool r)^"\n");*) r
end;;
(************************************************************************************)
module Ss_minisat_proc:SAT_SLV = functor (Sv:SV) ->
struct
  type t_var = Sv.t
  type nz_cons = t_var list list
  type p_var = (*include Gen.EQ_TYPE with type t=v*)
    | PVar of t_var
    | C_top
  type eq_syst = (t_var*t_var*p_var) list
  let stringofTvar = Sv.string_of
  let stringofPvar v = match v with | C_top -> "T" | PVar v -> Sv.string_of v
  let mkTop () = C_top
  let mkVar v = PVar v
  let getVar v = match v with | C_top -> None | PVar v -> Some v
  let string_of_eq (v1,v2,v3) = (Sv.string_of v1)^" * "^(Sv.string_of v2)^" = "^(match v3 with | PVar v3 ->  Sv.string_of v3 | _ -> " true")
  let string_of_eq_l l = String.concat "\n" (List.map string_of_eq l)
  (**********minisat interface **********)
  (* Global settings *)
  let minisat_timeout_limit = 15.0
  let test_number = ref 0
  let last_test_number = ref 0
  let minisat_restart_interval = ref (-1)
  let log_all_flag = ref false
  let is_minisat_running = ref false
  let in_timeout = ref 15.0 (* default timeout is 15 seconds *)
  let minisat_call_count: int ref = ref 0
  let log_file = open_out ("allinput.minisat")
  let minisat_input_mode = "file"    (* valid value is: "file" or "stdin" *)
  (*minisat*)
  let minisat_path = "/usr/local/bin/minisat"
  let minisat_name = "minisat"
  let minisat_arg = "-pre"
  let minisat_input_format = "cnf"   (* valid value is: cnf *)
  let number_clauses = ref 1
  let number_var = ref 0
  let minisat_process = ref {    PrvComms.name = "minisat";
                                 PrvComms.pid = 0;
                                 PrvComms.inchannel = stdin;
                                 PrvComms.outchannel = stdout;
                                 PrvComms.errchannel = stdin
                            }
  (***************************************************************
     INTERACTION
   **************************************************************)
  let rec collect_output (chn: in_channel)  : (string * bool) =
    try
      let line = input_line chn in
      if line = "SATISFIABLE" then
        (line, true)
      else
        collect_output chn
    with
    | End_of_file ->  ("", false)
  let get_prover_result (output : string) :bool =
    let validity =
      if (output="SATISFIABLE") then
        true
      else
        false in
    validity
  (* output:  - prover_output									- the running status of prover: true if running, otherwise false *)
  let get_answer (chn: in_channel) : (bool * bool)=
    let (output, running_state) = collect_output chn  in
    let
      validity_result = get_prover_result output;
    in
    (validity_result, running_state)
  let remove_file filename =
    try Sys.remove filename;
    with e -> ignore e
  let set_process proc =
    minisat_process := proc
  let start () =
    if not !is_minisat_running then (
      print_endline_quiet ("Starting Minisat... \n");
      last_test_number := !test_number;
      if (minisat_input_format = "cnf") then (
        PrvComms.start (minisat_name, minisat_path, [|minisat_arg|]) set_process;
        is_minisat_running := true;
      )
    )
  (* stop minisat system *)
  let stop () =
    if !is_minisat_running then (
      let num_tasks = !test_number - !last_test_number in
      print_string ("\nStop Minisat... " ^ (string_of_int !minisat_call_count) ^ " invocations "); flush stdout;
      let () = PrvComms.stop  !minisat_process num_tasks Sys.sigkill  in
      is_minisat_running := false;
    )
  (* restart Omega system *)
  let restart reason =
    if !is_minisat_running then (
      let () = print_string (reason ^ " Restarting minisat after ... " ^ (string_of_int !minisat_call_count) ^ " invocations ") in
      PrvComms.restart start stop
    )
    else (
      let () = print_string (reason ^ " not restarting minisat ... " ^ (string_of_int !minisat_call_count) ^ " invocations ") in ()
    )
  (* Runs the specified prover and returns output *)
  let check_problem_through_file (input: string) (timeout: float) : bool =
    (* debug *)
    (* let () = print_endline "** In function minisat.check_problem" in *)
    let file_suffix = Random.int 1000000 in
    let infile = "/tmp/in" ^ (string_of_int file_suffix) ^ ".cnf" in
    (*let () = print_endline ("-- input: \n" ^ input) in*)
    let out_stream = open_out infile in
    output_string out_stream input;
    close_out out_stream;
    let minisat_result="minisatres.txt" in
    let set_process proc = minisat_process := proc in
    let fnc () =
      if (minisat_input_format = "cnf") then (
        PrvComms.start (minisat_name, minisat_path, [|minisat_arg;infile;minisat_result|]) set_process;
        minisat_call_count := !minisat_call_count + 1;
        let (prover_output, running_state) = get_answer !minisat_process.PrvComms.inchannel in
        is_minisat_running := running_state;
        prover_output;
      )
      else failwith "[minisat.ml] The value of minisat_input_format is invalid!" in
    let res =
      try
        let fail_with_timeout () = restart ("[minisat]Timeout when checking sat!" ^ (string_of_float timeout)); false in
        let res = PrvComms.maybe_raise_and_catch_timeout fnc () timeout fail_with_timeout in
        res
      with _ -> ((* exception : return the safe result to ensure soundness *)
          Printexc.print_backtrace stdout;
          print_endline ("WARNING: Restarting prover due to timeout");
          Unix.kill !minisat_process.PrvComms.pid 9;
          ignore (Unix.waitpid [] !minisat_process.PrvComms.pid);
          false
        ) in
    let () = PrvComms.stop !minisat_process 0 9  in
    remove_file infile;
    res
  (**************************************************************
    MAIN INTERFACE : CHECKING IMPLICATION AND SATISFIABILITY
   *************************************************************)
  (*******************zzzzzzzzzzzzzz****************)
  (*generate the CNF *)
  let cnf_to_string var_cnt f : string =
    let fct l = String.concat " " (List.map (fun (c,b)-> if b then string_of_int c else ("-"^(string_of_int c))) l) in
    "p cnf "^(string_of_int var_cnt)^" "^ (string_of_int (List.length f))^"\n"^
    (String.concat " 0\n" (List.map fct f))^" 0\n"
  let xor sv1 sv2 sv3 = [ [(sv1, false);(sv2,false)];				(*~v1 | ~v2      *)
                          [(sv1,true);(sv2,true);(sv3,false)]; 	    (* v1 | v2 | ~v3 *)
                          [(sv1,false);(sv2,true);(sv3,true)]; 	    (* ~v1| v2 | v3  *)
                          [(sv1,true);(sv2,false);(sv3,true)]] 	 	(* v1 | ~v2| v3  *)
  let xorc sv1 sv2 = [[(sv1, true);(sv2,true)];[(sv1, false);(sv2,false)]]
  let trans_vv sv1 sv2 = [[(sv1, true);(sv2,false)];[(sv1, false);(sv2,true)]]
  let negVar v f = List.map (List.map (fun (c,b)-> if c=v then c,not b else c,b)) f
  let rec tauto l = match l with
    | [] -> false
    | (c,b)::t-> (List.exists (fun (v,b1)-> c=v && b<>b1) t) || (tauto t)
  let neg_f f =
    let f = List.map (List.map (fun (c,b)-> c,not b)) f in
    if f=[] then f
    else List.fold_left (fun a c->
        let r = List.concat (List.map (fun c-> List.map (fun d-> c::d) a) c) in
        List.filter (fun c->not (tauto c)) r) (List.map (fun c-> [c]) (List.hd f)) (List.tl f)
  let mkOr f1 f2 =
    let l = List.map (fun l -> List.map (fun l2 -> l@l2) f2) f1 in
    List.filter (fun c-> not (tauto c)) (List.concat l)
  let mkExists vl f =
    let fv = List.fold_left (fun a c-> a@ (List.map fst c)) [] f in
    let vl = List.filter (fun c-> List.mem c fv) vl in
    List.fold_left (fun f v-> mkOr f (negVar v f)) f vl
  let call_imply (a_ev:t_var list) (a_nz_cons:nz_cons) (a_l_eqs:eq_syst) (c_ev:t_var list) (c_nz_cons:nz_cons) (c_l_eqs:eq_syst) (c_const_vars:(t_var*bool) list) (c_subst_vars:(t_var*t_var) list):bool  =
    let ht = Hashtbl.create 20 in
    let tp = ref 0 in
    let get_var v = let v = Sv.string_of v in try Hashtbl.find ht v  with | Not_found -> (tp:= !tp+1; Hashtbl.add ht v !tp;!tp) in
    let trans_eq (v1,v2,c) = match c with
      | C_top -> xorc (get_var v1) (get_var v2)
      | PVar v3-> xor (get_var v1) (get_var v2) (get_var v3) in
    let ante_f =
      let nz = List.map (List.map (fun c-> get_var c, true)) a_nz_cons in   (*conj of disj*)
      let eqs = List.map trans_eq a_l_eqs in
      let a_ev = List.map get_var a_ev in
      mkExists a_ev (List.concat (nz::eqs)) in
    let conseq_f =
      let c_ev = List.map get_var c_ev in
      let nz = List.map (List.map (fun c-> get_var c, true)) c_nz_cons in   (*conj of disj*)
      let eqs = List.map trans_eq  c_l_eqs in
      let c_subst = List.map (fun (v1,v2) -> trans_vv (get_var v1)(get_var v2)) c_subst_vars in
      let c_const = List.map (fun (v,b) -> [[(get_var v, b)]]) c_const_vars in
      let r = List.concat (nz::eqs@c_subst@c_const) in
      let r = List.map (List.filter (fun (c,_)-> not (List.mem c c_ev))) (neg_f r) in
      List.filter (fun c-> c<>[]) r in
    let all_f = ante_f@conseq_f in
    if all_f<>[] then
      not (check_problem_through_file (cnf_to_string !tp (ante_f@conseq_f)) 0.)
    else true
  let call_imply  (a_ev:t_var list) (a_nz_cons:nz_cons) (a_l_eqs:eq_syst)
      (c_ev:t_var list) (c_nz_cons:nz_cons) (c_l_eqs:eq_syst) (c_const_vars:(t_var*bool) list) (c_subst_vars:(t_var*t_var) list):bool  =
    (* to delete *)
    (* let nzsf l = String.concat "," (List.map (fun l-> "{"^(String.concat "," (List.map Sv.string_of l))^"}") l) in *)
    (* let pr_list f l = String.concat "\n" (List.map f l) in *)
    (* let pr_pair f1 f2 (x1,x2) = "("^(f1 x1)^","^(f2 x2)^")" in *)
    (* let consl = pr_list (pr_pair Sv.string_of string_of_bool) c_const_vars in *)
    (* let cvel = pr_list (pr_pair Sv.string_of Sv.string_of) c_subst_vars in *)
    (* let anzs = nzsf a_nz_cons in *)
    (* let cnzs = nzsf c_nz_cons in *)
    (* let aeqss = string_of_eq_l a_l_eqs in *)
    (* let ceqss = string_of_eq_l c_l_eqs in *)
    (* print_string ("MINISAT IMPLY\n ante: nz: "^anzs^";\n ex: "^(pr_list Sv.string_of a_ev)^";\n eqs: "^aeqss^";\n"); *)
    (* print_string ("conseq: nz: "^cnzs^";\n ex: "^(pr_list Sv.string_of c_ev)^";\n veq: "^cvel^";\n cons: "^consl^";\n eqs: "^ceqss^";\n"); *)
    (* to delete *)
    let r = call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars in
    (*print_string ("r: "^(string_of_bool r));*)
    r
  let call_sat non_zeros eqs =
    let ht = Hashtbl.create 20 in
    let tp = ref 0 in
    let get_var v = let v = Sv.string_of v in try Hashtbl.find ht v  with | Not_found ->
        (tp:= !tp+1;
         (*print_string (v^" "^(string_of_int !tp)^"\n");*)						Hashtbl.add ht v !tp;!tp) in
    let input =
      let nz = List.map (List.map (fun c-> get_var c, true)) non_zeros in   (*conj of disj*)
      let eqs = List.map ( fun (v1,v2,c)->
          let sv1 = get_var v1 in
          let sv2 = get_var v2 in
          match c with
          | C_top -> xorc sv1 sv2
          | PVar v3-> xor sv1 sv2 (get_var v3) ) eqs in
      List.concat (nz::eqs) in
    if input<> [] then
      let input_str = cnf_to_string !tp input in
      (*print_string (input_str^"\n");*)
      check_problem_through_file input_str minisat_timeout_limit
    else true
  let call_sat non_zeros eqs =
    (* to delete *)
    (* let nzs = String.concat "," (List.map (fun l-> "{"^(String.concat "," (List.map Sv.string_of l))^"}") non_zeros) in *)
    (* let eqss = string_of_eq_l eqs in *)
    (* print_string ("MINISAT SAT: "^nzs^"\n"^eqss^"\n"); *)
    (* (\* to delete *\) *)
    let r = call_sat non_zeros eqs in
    (*print_string ("r: "^(string_of_bool r)^"\n");*) r
end;;
module Solver_Z3 = Share_prover.Dfrac_s_solver(Ts)(Share_prover.Sv)(Ss_Z3_proc)
module Solver_mini = Share_prover.Dfrac_s_solver(Share_prover.Ts)(Share_prover.Sv)(Ss_minisat_proc)
module Solver = Solver_mini
module Eqs =
struct
  type var = Sv.t
  type const = Ts.stree
  type pcvar = Solver.frac_perm
  type eq = Solver.eq
  type eq_syst = Solver.eq_syst
  let mkVar = Sv.var_of
  let mkEq v1 v2 v3 = (v1,v2,v3)
  let mkEqS l1 l2 l3 l4 l5= {Solver.eqs_ex = l1; Solver.eqs_nzv = l2; Solver.eqs_ve=l3; Solver.eqs_vc=l4; Solver.eqs_eql = l5}
  let mkcFull = Ts.top
  let mkcEmpty = Ts.bot
  let mkcNode = Ts.mkNode
  let mkpcCnst c = Solver.Cperm c
  let mkpcVar v = Solver.Vperm v
end;;
type cmd =
  | Sat of Eqs.eq_syst
  | Imply of Eqs.eq_syst * Eqs.eq_syst;;
