#include "xdebug.cppo"
open VarGen
(*
  Choose with theorem prover to prove formula
*)

open Globals
open Others
open GlobProver
open Gen.Basic
open Mcpure
open Cpure
open Mcpure_D
open Log
open Printf
open Label_aggr

module CP = Cpure
module MCP = Mcpure
module NM = Auxnorm

(* module LO = Label_only.Lab_List *)
module LO = Label_only.LOne

(* let wrap_redlog_only f a = *)
(*   wrap_one_bool Redlog.dis_omega true f a *)

(* let wrap_oc_redlog f a = *)
(*   wrap_one_bool Redlog.dis_omega false f a *)

let wrap_redlog = Wrapper.wrap_one_bool Redlog.dis_omega true
let wrap_ocredlog = Wrapper.wrap_one_bool Redlog.dis_omega false

let test_db = false

(* let pure_tp = ref OmegaCalc *)
(* let tp = ref OmegaCalc *)

(* WN : why do we have pure_tp (prover-code) and prover_arg (string) *)
(* let pure_tp = ref OM *)
let pure_tp = ref Z3
(* let tp = ref Redlog *)
(* let tp = ref AUTO *)
(*For conc-r, z3 for relations, mona for bags, redlog for fractions *)
(* let tp = ref PARAHIP *)
(* let tp = ref Z3 *)

let get_tp_code () = 
  let pr = !pure_tp in
  string_of_prover_code pr


let provers_process = ref None

type prove_type = Sat of CP.formula | Simplify of CP.formula | Imply of CP.formula * CP.formula
type result_type = Timeout | Result of string | Failure of string

let print_pure = ref (fun (c:CP.formula)-> Cprinter.string_of_pure_formula c(*" printing not initialized"*))

(* let prover_arg = ref "oc" *)
let prover_arg = ref "z3" (* default prover *)
let user_choice = ref false

(* let prover_arg = ref "om" *)
let external_prover = ref false
let tp_batch_mode = ref true
let external_host_ports = ref []
let webserver = ref false
let priority = ref 1
let decr_priority = ref false
let set_priority = ref false
let prio_list = ref []

let sat_cache = ref (Hashtbl.create 200)
let imply_cache = ref (Hashtbl.create 200)

(* An Hoa : Global variablew the prover interface to pass message to this interface *)

let generated_prover_input = ref "_input_not_set_"

let prover_original_output = ref "_output_not_set_"

let set_generated_prover_input inp =
  generated_prover_input := inp;;

let reset_generated_prover_input () = generated_prover_input := "_input_not_set_";;

let get_generated_prover_input () = !generated_prover_input;;

let set_prover_original_output oup = 
  prover_original_output := oup;;

let reset_prover_original_output () = prover_original_output := "_output_not_set_";;

let get_prover_original_output () = !prover_original_output;;

let suppress_imply_out = ref true;;

Smtsolver.set_generated_prover_input := set_generated_prover_input;;
Smtsolver.set_prover_original_output := set_prover_original_output;;
Z3.set_generated_prover_input := set_generated_prover_input;;
Z3.set_prover_original_output := set_prover_original_output;;
Omega.set_generated_prover_input := set_generated_prover_input;;
Omega.set_prover_original_output := set_prover_original_output;;

(* An Hoa : end *)

module Netprover = struct
  let debuglevel = 0 
  let trace f s = if debuglevel <= 1 then (prerr_string (Printf.sprintf "\n%d: %s: %s" (Unix.getpid ()) f s); flush stderr) else ()
  let show_info f s = if debuglevel <= 2 then (prerr_string (Printf.sprintf "\n%d: %s: %s" (Unix.getpid ()) f s); flush stderr) else ()

  (* server-setting (prover-setting) -> ()                                 *)
  (* proc_group(reqid,[[task]],timeout) -> [result]                        *)
  (* proc_group_async(reqid,[[task]]) -> groupid                           *)
  (* wait(groupid,[taskid::int],timeout) -> [result] timeout of -1 :       *)
  (* indefinite kill(groupid,[taskid])                                     *)
  (* wait_and_kill(groupid,[taskid::int],timeout) -> [result] timeout of   *)
  (* -1 : indefinite                                                       *)
  let use_pipe = ref false
  let in_ch = ref stdin
  let out_ch = ref stdout
  let default_pipe = "default"
  let default_timeout = 200.0
  let seq_number = ref 0 (* for asynch calls in the future *)
  let get_seq_no () = incr seq_number; !seq_number

  let start_prover_process () =
    (* let () = print_string ("\n Tpdispatcher: start_prover_process \n") in *)
    let is_running cmd_args =
      let cmd = "ps -u$USER -f" in
      let ch = Unix.open_process_in cmd in
      try
        let re = Str.regexp_string cmd_args in
        while true do
          let s = input_line ch in
          try
            if Str.search_forward re s 0 >= 0 then raise Exit
          with Not_found -> ()
        done;
        false
      with Exit -> true
         | End_of_file -> false
         | e -> print_string "ho"; flush stdout; false
    in
    let cmd_args = "prover --pipe " ^ default_pipe in
    if not (is_running cmd_args) then begin
      print_string "\nLaunching default prover\n."; flush stdout;
      ignore(Unix.system cmd_args)
    end

  let set_use_pipe () =
    start_prover_process ();
    external_prover := true;
    use_pipe := true;
    let i, o = Net.Pipe.init_client default_pipe in
    in_ch := i; out_ch := o

  let set_use_socket host_port =
    external_prover := true ;
    use_pipe := false;
    let i, o = Net.Socket.init_client host_port in
    in_ch := i; out_ch := o

  let set_use_socket_map host_port =
    external_prover := true ;
    use_pipe := false;
    let i, o = Net.Socket.init_client host_port in
    in_ch := i; out_ch := o

  let set_use_socket_for_web host_port =
    external_host_ports := [host_port];
    external_prover := true;
    use_pipe := false;
    let i, o = Net.Socket.init_client host_port in
    in_ch := i; out_ch := o

  let set_prio_list str =
    try
      set_priority := true;
      let lst = Str.split (Str.regexp ";") str in
      prio_list := List.map (fun name_prio -> let l = Str.split (Str.regexp ":") name_prio in ((List.hd l),int_of_string(List.nth l 1))) lst
    with e -> print_endline_quiet "set_prio_list error"; raise e

  let index_of elem lst =
    (** return the first index of [elem] in the list [lst] *)
    let rec find i elem lst =
      match lst with
      | [] -> (- 1)
      | hd:: tl -> if elem = hd then i else find (i + 1) elem tl
    in find 0 elem lst

  exception ServerTimeout
  exception ParStop

  type pmap_result = One of string | All of string list | Unknown

  let pmap (provers: string) (jobs: prove_type list) (stopper: result_type -> bool) : pmap_result =
    (* [pmap] sends the tuple of [provers] and [jobs] list to the server   *)
    (* and wait for results. When a result arrives, the [stopper] function *)
    (* is applied to the result. If [stopper] returns true, the function   *)
    (* exits with the result arrives. Otherwise it continues until all of  *)
    (* the results arrives and return the whole list of results.           *)

    let send_stop seqno = Net.IO.write !out_ch (Net.IO.msg_type_cancel_job, seqno) in
    (* send out job list to server *)
    let seqno = get_seq_no () in
    (* let stopper_closure = Marshal.to_string stopper [Marshal.Closures] in   *)
    (* trace "closure=" stopper_closure;                                       *)
    Net.IO.write_job_to_master !out_ch seqno default_timeout provers jobs "true";

    (* collect the results *)
    let num_jobs = List.length jobs in
    let result_arr = Array.make num_jobs "" in
    let time_start = Unix.gettimeofday () in
    try
      let num_results = ref 0 in
      let wait_fd = Unix.descr_of_in_channel !in_ch in
      while !num_results < num_jobs do
        let time_left = default_timeout -. ((Unix.gettimeofday ()) -. time_start) in
        if time_left < 0. then
          failwith "timeout" 
        else begin
          (* show_info "pmap" (Printf.sprintf "wait %d results" (num_jobs -          *)
          (* !num_results));                                                         *)
          let in_fds, _, _ = Gen.Basic.restart  (Unix.select [wait_fd] [] []) time_left in
          (* let in_fds, _, _ = Unix.select [wait_fd] [] [] time_left in *)
          if in_fds <> [] then begin
            incr num_results;
            let seqno, idx, result = Net.IO.read_result (Unix.in_channel_of_descr (List.hd in_fds)) in
            match result with
            | Result s ->
              if idx >= 0 then begin
                (* trace "pmap" (Printf.sprintf "idx = %d" idx); *)
                let res = Net.IO.from_string s in
                Array.set result_arr idx s;
                if stopper res then begin
                  show_info "pmap: discard others" "";
                  send_stop seqno;
                  Array.set result_arr 0 s; (* will return the first element only *)
                  raise ParStop
                end
              end else
                show_info "pmap result" "index is negative"
            | Timeout -> trace "pmap result" " timed out."
            | Failure s -> trace "pmap result" s
          end;
        end
      done;
      All (List.filter (fun s -> s <> "") (Array.to_list result_arr))
    with
    | ParStop -> trace "pmap" "\n by stoper."; (One result_arr.(0))
    | ServerTimeout -> trace "pmap" "\npmap timed out."; Unknown
    | e -> trace "pmap" (Printexc.to_string e); Unknown

  let call_prover ( f : prove_type) = 
    (** send message to external prover to get the result. *)
    try
      let ret = pmap !prover_arg [f] (fun _ -> false) in
      match ret with Unknown -> None 
                   | One s ->   if s <> "" then Some (Net.IO.from_string s) else None
                   | All results -> let s = (List.hd results) in
                     if s <> "" then Some (Net.IO.from_string s) else None
    with e -> trace "pmap" (Printexc.to_string e); None

end

(* ##################################################################### *)

(* class used for keeping prover's functions needed for the incremental proving*)
class incremMethods : [CP.formula] incremMethodsType = object
  val push_no = ref 0 (*keeps track of the number of saved states of the current process*) 
  val process_context = ref [] (*variable used to archives all the assumptions send to the current process *)
  val declarations = ref [] (*variable used to archive all the declared variables in the current process context *) (* (stack_no * var_name * var_type) list*)
  val process = ref None (* prover process *)

  (*creates a new proving process *)
  method start_p () : prover_process_t =
    let proc = 
      match !pure_tp with
      | Cvc4 -> Cvc4.start()
      | _ -> Cvc4.start() (* to be completed for the rest of provers that support incremental proving *) 
    in 
    process := Some proc;
    proc

  (*stops the proving process*)
  method stop_p (process: prover_process_t): unit =
    match !pure_tp with
    | Cvc4 -> Cvc4.stop process
    | _ -> () (* to be completed for the rest of provers that support incremental proving *)

  (*saves the state of the process and its context *)
  method push (process: prover_process_t): unit = 
    push_no := !push_no + 1;
    match !pure_tp with
    | Cvc4 -> Cvc4.cvc4_push process
    | _ -> () (* to be completed for the rest of provers that support incremental proving *)

  (*returns the process to the state it was before the push call *)
  method pop (process: prover_process_t): unit = 
    match !pure_tp with
    | Cvc4 -> Cvc4.cvc4_pop process
    | _ -> () (* to be completed for the rest of provers that support incremental proving *)

  (*returns the process to the state it was before the push call on stack n *)
  method popto (process: prover_process_t) (n: int): unit = 
    let n = 
      if ( n > !push_no) then begin
        x_dinfo_zp (lazy ("\nCannot pop to " ^ (string_of_int n) ^ ": no such stack. Will pop to stack no. " ^ (string_of_int !push_no))) no_pos;
        !push_no 
      end
      else n in
    match !pure_tp with
    (* | Cvc4 -> Cvc4.cvc4_popto process n *)
    | _ -> () (* to be completed for the rest of provers that support incremental proving *)

  method imply (process: (prover_process_t option * bool) option) (ante: CP.formula) (conseq: CP.formula) (imp_no: string): bool = true
  (* let () = match proceess with  *)
  (*   | Some (Some proc, send_ante) -> if (send_ante) then  *)
  (*       else *)
  (*      imply process ante conseq imp_no *)

  (*adds active assumptions to the current process*)
  (* method private add_to_context assertion: unit = *)
  (*     process_context := [assertion]@(!process_context) *)

  method set_process (proc: prover_process_t) =
    process := Some proc

  method get_process () : prover_process_t option =
    !process 

end

let incremMethodsO = ref (new incremMethods)


(* ##################################################################### *)

let rec check_prover_existence prover_cmd_str =
  match prover_cmd_str with
  | [] -> ()
  | "log"::rest -> check_prover_existence rest
  | prover::rest -> 
    let _ = x_dinfo_hp (add_str "check prover" pr_id) prover no_pos in
    (* let exit_code = Sys.command ("which "^prover) in *)
    (* Do not display system info in the website *)
    (* let () = print_endline ("prover:" ^ prover) in *)
    let prover = 
      if String.compare prover "z3n" = 0 then "z3-4.2" 
      else if String.compare prover "mona" = 0 then try FileUtil.which "mona" with Not_found -> ""
      else prover
    in
    let exit_code = Sys.command ("which "^prover^" > /dev/null 2>&1") in
    if exit_code > 0 then
      if  (Sys.file_exists prover) then
        let _ =
          if String.compare prover "oc" = 0 then
            let () = Omega.is_local_solver := true in
            let () = Omega.omegacalc := "./oc" in
            ()
          else if String.compare prover "z3" = 0 then
            let () = Smtsolver.is_local_solver := true in
            let () = Smtsolver.smtsolver_name := "./z3" in
            ()
          else ()
        in
        check_prover_existence rest
      else
        let () = print_string ("WARNING : Command for starting the prover (" ^ prover ^ ") not found\n") in
        exit 0
    else check_prover_existence rest

let is_smtsolver_z3 tp_str=
  (* try *)
  (*    if (String.sub tp_str 0 4) = "./z3" || (String.sub tp_str 0 2) = "z3" then *)
  (*      true *)
  (*    else false *)
  (*  with _ ->  if (String.sub tp_str 0 2) = "z3" then *)
  (*    true else false *)
  String.compare tp_str "./z3" = 0 || String.compare tp_str "z3" = 0


let set_tp user_flag tp_str =
  prover_arg := tp_str;
  user_choice := user_flag;
  (******we allow normalization/simplification that may not hold
         in the presence of floating point constraints*)
  (* let () = print_endline ("solver:" ^ tp_str) in *)
  let () = x_binfo_pp (* print_endline_quiet *) ("set_tp " ^ tp_str) no_pos in 
  if tp_str = "parahip" || tp_str = "rm" then allow_norm := false else allow_norm:=true;
  (**********************************************)
  let redcsl_str = if !Globals.web_compile_flag then try FileUtil.which "redcsl" with Not_found -> "" else "redcsl" in
  let prover_str = ref [] in
  (*else if tp_str = "omega" then
    	(tp := OmegaCalc; prover_str := "oc"::!prover_str;)*)
  if (* (String.sub tp_str 0 2) = "oc" *) String.compare tp_str "./oc" = 0 || String.compare tp_str "oc" = 0 then
    (Omega.omegacalc := tp_str; pure_tp := OmegaCalc; prover_str := "oc"::!prover_str;)
  else if tp_str = "dp" then pure_tp := DP
  else if tp_str = "cvcl" then 
    (pure_tp := CvcLite; prover_str := "cvcl"::!prover_str;)
  else if tp_str = "cvc4" then 
    (pure_tp := Cvc4; prover_str := "cvc4"::!prover_str;)
  else if tp_str = "co" then
    (pure_tp := CO; prover_str := "cvc4"::!prover_str; 
     prover_str := "oc"::!prover_str;)
  else if tp_str = "isabelle" then
    (pure_tp := Isabelle; prover_str := "isabelle-process"::!prover_str;)
  else if tp_str = "mona" then
    (pure_tp := Mona; prover_str := "mona"::!prover_str;)
  else if tp_str = "monah" then
    (pure_tp := MonaH; prover_str := "mona"::!prover_str;)
  else if tp_str = "om" then
    (pure_tp := OM; prover_str := "oc"::!prover_str;
     prover_str := "mona"::!prover_str;)
  else if tp_str = "oi" then
    (pure_tp := OI; prover_str := "oc"::!prover_str;
     prover_str := "isabelle-process"::!prover_str;)
  else if tp_str = "set" then
    (pure_tp := SetMONA; prover_str := "mona"::!prover_str;)
  else if tp_str = "cm" then
    (pure_tp := CM; prover_str := "cvc4"::!prover_str;
     prover_str := "mona"::!prover_str;)
  else if tp_str = "coq" then
    (pure_tp := Coq; prover_str := "coqtop"::!prover_str;)
    (*else if tp_str = "z3" then 
      	(pure_tp := Z3; prover_str := "z3"::!prover_str;)*)
  else
    (* if (String.sub tp_str 0 4) = "./z3" || (String.sub tp_str 0 2) = "z3" then *)
    (*     (Smtsolver.smtsolver_name := tp_str; pure_tp := Z3; prover_str := "z3"::!prover_str;) *)
  if is_smtsolver_z3 tp_str then
    (Smtsolver.smtsolver_name := tp_str; pure_tp := Z3; prover_str := "z3"::!prover_str;)
  else if tp_str = "z3n" then
    (Z3.smtsolver_name := tp_str; pure_tp := Z3N; prover_str := "z3n"::!prover_str;)
  else if tp_str = "z3-4.3.1" then
    (Smtsolver.smtsolver_name := tp_str; pure_tp := Z3; prover_str := "z3-4.3.1"::!prover_str;)
  else if tp_str = "redlog" then
    (pure_tp := Redlog; prover_str := redcsl_str::!prover_str;)
  else if tp_str = "OCRed" then
    (pure_tp := OCRed; prover_str := "oc"::redcsl_str::!prover_str;)
  else if tp_str = "math" then
    (pure_tp := Mathematica; prover_str := "mathematica"::!prover_str;)
  else if tp_str = "rm" then
    pure_tp := RM
  else if tp_str = "parahip" then
    (pure_tp := PARAHIP;
     prover_str := "z3"::!prover_str;
     prover_str := "mona"::!prover_str;
     prover_str := redcsl_str::!prover_str;)
  else if tp_str = "zm" then
    (pure_tp := ZM; 
     prover_str := "z3"::!prover_str;
     prover_str := "mona"::!prover_str;)
  else if tp_str = "auto" then
    (pure_tp := AUTO; prover_str := "oc"::!prover_str;
     prover_str := "z3"::!prover_str;
     prover_str := "mona"::!prover_str;
     (* prover_str := "coqtop"::!prover_str; *)
    )
  else if tp_str = "oz" then
    (pure_tp := AUTO; prover_str := "oc"::!prover_str;
     prover_str := "z3"::!prover_str;
    )
  else if tp_str = "prm" then
    (Redlog.is_presburger := true; pure_tp := RM)
  else if tp_str = "spass" then
    (pure_tp := SPASS; prover_str:= "SPASS-MOD"::!prover_str)
  else if tp_str = "minisat" then
    (pure_tp := MINISAT; prover_str := "z3"::!prover_str;)
  else if tp_str = "log" then
    (pure_tp := LOG; prover_str := "log"::!prover_str)
  else
    ();
  if not !Globals.is_solver_local then check_prover_existence !prover_str else ()

let set_tp user_flag tp_str =
  (* print_endline_quiet ("set_tp "^tp_str); *)
  Debug.no_1 "set_tp" pr_id pr_none (set_tp user_flag) tp_str

let init_tp () =
  let () = x_dinfo_hp (add_str "init_tp:user_choice" string_of_bool) !user_choice no_pos in
  if not(!user_choice) then
    begin
      let () = (if !Globals.is_solver_local then
                  let () = Smtsolver.is_local_solver := true in
                  let () = Smtsolver.smtsolver_name := "z3" in
                  let () = Omega.is_local_solver := true in
                  let () = Omega.omegacalc := "./oc" in
                  ()
                else ()) in
      let () = x_binfo_pp ("init_tp by default: ") no_pos in 
      x_add_1 set_tp false !Smtsolver.smtsolver_name (* "z3" *)
      (* set_tp "parahip" *)
    end

let pr_p = pr_pair Cprinter.string_of_spec_var Cprinter.string_of_formula_exp

let imm_stk = new Gen.stack_pr "imm-stk" pr_p (fun (x,_) (y,_) -> CP.eq_spec_var x y )

let string_of_tp tp = match tp with
  | OmegaCalc -> "omega"
  | CvcLite -> "cvcl"
  | Cvc4 -> "cvc4"
  | CO -> "co"
  | Isabelle -> "isabelle"
  | Mona -> "mona"
  | MonaH -> "monah"
  | OM -> "om"
  | OI -> "oi"
  | SetMONA -> "set"
  | CM -> "cm"
  | Coq -> "coq"
  | Z3 -> "z3"
  | Z3N -> "z3n"
  | Redlog -> "redlog"
  | OCRed -> "OC/redlog"
  | Mathematica -> "mathematica"
  | RM -> "rm"
  | PARAHIP -> "parahip"
  | ZM -> "zm"
  | OZ -> "oz"
  | AUTO -> "auto"
  | DP -> "dp"
  | SPASS -> "spass"
  | MINISAT -> "minisat"
  | LOG -> "log"

let name_of_tp tp = match tp with
  | OmegaCalc -> "Omega Calculator"
  | CvcLite -> "CVC Lite"
  | Cvc4 -> "CVC4"
  | CO -> "CVC Lite and Omega"
  | Isabelle -> "Isabelle"
  | Mona -> "Mona"
  | MonaH -> "MonaH"
  | OM -> "Omega and Mona"
  | OI -> "Omega and Isabelle"
  | SetMONA -> "Set Mona"
  | CM -> "CVC Lite and Mona"
  | Coq -> "Coq"
  | Z3 -> "Z3"
  | Z3N -> "Z3N"
  | Redlog -> "Redlog"
  | OCRed -> "OC/Redlog"
  | Mathematica -> "Mathematica"
  | RM -> "Redlog and Mona"
  | PARAHIP -> "Redlog, Z3, and Mona"
  | ZM -> "Z3 and Mona"
  | OZ -> "Omega, Z3"
  | AUTO -> "Omega, Z3, Mona, Coq"
  | DP -> "DP"
  | SPASS -> "SPASS"
  | MINISAT -> "MINISAT"
  | LOG -> "LOG"

let log_file_of_tp tp = match tp with
  | OmegaCalc -> "allinput.oc"
  | Cvc4 -> "allinput.cvc4"
  | Isabelle -> "allinput.thy"
  | Mona -> "allinput.mona"
  | Coq -> "allinput.v"
  | Redlog -> "allinput.rl"
  | OCRed -> "allinput.rl"
  | Mathematica -> "allinput.math"
  | Z3 -> "allinput.z3"
  | Z3N -> "allinput.z3n"
  | AUTO -> "allinput.auto"
  | OZ -> "allinput.oz"
  | SPASS -> "allinput.spass"
  | _ -> ""

let get_current_tp_name () = name_of_tp !pure_tp

let omega_count = ref 0

let start_prover () =
  match !pure_tp with
  | Coq -> Coq.start ();
  | Redlog | OCRed | RM -> Redlog.start ();
  | Cvc4 -> (
      provers_process := Some (Cvc4.start ()); (* because of incremental *)
      let () = match !provers_process with 
        |Some proc ->  !incremMethodsO#set_process proc
        | _ -> () in
      Omega.start_prover ();
    )
  | Mona -> Mona.start()
  | Mathematica -> Mathematica.start()
  | Isabelle -> (
      Isabelle.start();
      Omega.start_prover();
    )
  | OM -> (
      Mona.start();
      Omega.start_prover();
    )
  | ZM -> (
      Mona.start();
      Smtsolver.start();
    )
  | DP -> Smtsolver.start();
  | Z3 -> Smtsolver.start();
  | Z3N -> Z3.start();
  | SPASS -> Spass.start();
  | LOG -> file_to_proof_log !Globals.source_files
  | MINISAT -> Minisat.start ()
  | _ -> Omega.start_prover()

let start_prover () =
  Gen.Profiling.do_1 "TP.start_prover" start_prover ()

let stop_prover () =
  match !pure_tp with
  | OmegaCalc -> (
      Omega.stop ();
      if !Redlog.is_reduce_running then Redlog.stop ();
    )
  | Coq -> Coq.stop ();
  | OCRed | Redlog | RM -> (
      Redlog.stop();
      Omega.stop();
    )
  | Cvc4 -> (
      let () = match !provers_process with
        |Some proc ->  Cvc4.stop proc;
        |_ -> () in
      Omega.stop();
    )
  | Isabelle -> (
      Isabelle.stop();
      Omega.stop();
    )
  | Mona -> Mona.stop();
  | Mathematica -> Mathematica.stop();
  | OM -> (
      if !Mona.is_mona_running then
        Mona.stop();
      if !Omega.is_omega_running then
        Omega.stop();
    )
  | ZM -> (
      Mona.stop();
      Smtsolver.stop();
    )
  | DP -> Smtsolver.stop()
  | Z3 -> (Smtsolver.stop();
           (*in the website, use z3, oc keeps running although hip is stopped*)
           if !Omega.is_omega_running then Omega.stop ();)
  | Z3N -> (Z3.stop();
            (*in the website, use z3, oc keeps running although hip is stopped*)
            if !Omega.is_omega_running then Omega.stop ();)
  | SPASS -> Spass.stop();
  | MINISAT -> Minisat.stop ();
  | _ -> Omega.stop();;

let stop_prover () =
  Gen.Profiling.do_1 "TP.stop_prover" stop_prover ()

(* Method checking whether a formula contains bag constraints or BagT vars *)

let is_bag_b_constraint (pf,_) = match pf with
  | CP.BConst _ 
  | CP.BVar _
  | CP.Lt _ 
  | CP.Lte _ 
  | CP.Gt _ 
  | CP.Gte _
  | CP.EqMax _ 
  | CP.EqMin _
  | CP.ListIn _ 
  | CP.ListNotIn _
  | CP.ListAllN _ 
  | CP.ListPerm _
    -> Some false
  | CP.BagIn _ 
  | CP.BagNotIn _
  | CP.BagMin _ 
  | CP.BagMax _
  | CP.BagSub _
    -> Some true
  | _ -> None

let is_bag_constraint (e: CP.formula) : bool =  
  let f_e e = match e with
    | CP.Bag _
    | CP.BagUnion _
    | CP.BagIntersect _
    | CP.BagDiff _ 
      -> Some true
    | CP.Var (CP.SpecVar (t, _, _), _) -> 
      (match t with
       | BagT _ -> Some true
       | _ -> Some false)
    | _ -> Some false
  in
  let or_list = List.fold_left (||) false in
  CP.fold_formula e (nonef, is_bag_b_constraint, f_e) or_list

let rec is_memo_bag_constraint (f:memo_pure): bool = 
  List.exists (fun c-> 
      (List.exists is_bag_constraint c.memo_group_slice)|| 
      (List.exists (fun c-> match is_bag_b_constraint c.memo_formula with | Some b-> b |_ -> false) c.memo_group_cons)
    ) f

(* TODO : make this work for expression *)
let rec is_array_exp e = match e with
  | CP.List _
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListAppend _
  | CP.ListReverse _ ->
    Some false
  | CP.Add (e1,e2,_)
  | CP.Subtract (e1,e2,_)
  | CP.Mult (e1,e2,_)
  | CP.Div (e1,e2,_)
  | CP.Max (e1,e2,_)
  | CP.Min (e1,e2,_)
  | CP.BagDiff (e1,e2,_) -> (
      match (is_array_exp e1) with
      | Some true -> Some true
      | _ -> is_array_exp e2
    )
  | CP.Bag (el,_)
  | CP.BagUnion (el,_)
  | CP.BagIntersect (el,_) -> (
      List.fold_left (fun res exp -> match res with
          | Some true -> Some true
          | _ -> is_array_exp exp) (Some false) el
    )
  | CP.ArrayAt (_,_,_) -> Some true
  | CP.Template _ -> Some false
  | CP.Func _ -> Some false
  | CP.TypeCast (_, e1, _) -> is_array_exp e1
  | CP.AConst _ | CP.FConst _ | CP.IConst _ | CP.Tsconst _ | CP.InfConst _ 
  | CP.NegInfConst _
  | CP.Bptriple _
  | CP.Tup2 _
  | CP.Level _
  | CP.Var _ | CP.Null _ -> Some false

(* Method checking whether a formula contains list constraints *)
let rec is_list_exp e = match e with
  | CP.List _
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListAppend _
  | CP.ListReverse _ -> Some true
  | CP.Add (e1,e2,_)
  | CP.Subtract (e1,e2,_)
  | CP.Mult (e1,e2,_)
  | CP.Div (e1,e2,_)
  | CP.Max (e1,e2,_)
  | CP.Min (e1,e2,_)
  | CP.BagDiff (e1,e2,_) -> (
      match (is_list_exp e1) with
      | Some true -> Some true
      | _ -> is_list_exp e2
    )
  | CP.Bag (el,_)
  | CP.BagUnion (el,_)
  | CP.BagIntersect (el,_) -> (
      List.fold_left (fun res exp -> match res with
          | Some true -> Some true
          | _ -> is_list_exp exp) (Some false) el
    )
  | CP.TypeCast (_, e1, _) -> is_list_exp e1
  | CP.ArrayAt (_,_,_) | CP.Func _ | CP.Template _ -> Some false
  | CP.Null _ | CP.AConst _ | CP.Tsconst _ | CP.InfConst _ | CP.NegInfConst _
  | CP.Bptriple _
  | CP.Tup2 _
  | CP.Level _
  | CP.FConst _ | CP.IConst _ -> Some false
  | CP.Var(sv,_) -> if CP.is_list_var sv then Some true else Some false

(*let f_e e = Debug.no_1 "f_e" (Cprinter.string_of_formula_exp) (fun s -> match s with
  	| Some ss -> string_of_bool ss
  	| _ -> "") f_e_1 e
*)	

(* TODO : where are the array components *)
let is_array_b_formula (pf,_) = match pf with
  | CP.BConst _ | CP.XPure _ | CP.Frm _
  | CP.BVar _
  | CP.BagMin _ 
  | CP.BagMax _
  | CP.SubAnn _
  | CP.LexVar _
    -> Some false
  | CP.Lt (e1,e2,_) 
  | CP.Lte (e1,e2,_) 
  | CP.Gt (e1,e2,_)
  | CP.Gte (e1,e2,_)
  | CP.Eq (e1,e2,_)
  | CP.Neq (e1,e2,_)
  | CP.BagSub (e1,e2,_)
    -> (match (is_array_exp e1) with
        | Some true -> Some true
        | _ -> is_array_exp e2)
  | CP.EqMax (e1,e2,e3,_)
  | CP.EqMin (e1,e2,e3,_)
    -> (match (is_array_exp e1) with
        | Some true -> Some true
        | _ -> (match (is_array_exp e2) with
            | Some true -> Some true
            | _ -> is_array_exp e3))
  | CP.BagIn (_,e,_) 
  | CP.BagNotIn (_,e,_)
    -> is_array_exp e
  | CP.ListIn _ 
  | CP.ListNotIn _
  | CP.ListAllN _ 
  | CP.ListPerm _
  | CP.ImmRel _ 
    -> Some false
  | CP.RelForm _ -> Some true
(* | CP.VarPerm _ -> Some false *)

let is_list_b_formula (pf,_) = match pf with
  | CP.BConst _ 
  | CP.BVar _
  | CP.BagMin _ 
  | CP.BagMax _
    -> Some false    
  | CP.Lt (e1,e2,_) 
  | CP.Lte (e1,e2,_) 
  | CP.Gt (e1,e2,_)
  | CP.Gte (e1,e2,_)
  | CP.Eq (e1,e2,_)
  | CP.Neq (e1,e2,_)
  | CP.BagSub (e1,e2,_)
    -> (match (is_list_exp e1) with
        | Some true -> Some true
        | _ -> is_list_exp e2)
  | CP.EqMax (e1,e2,e3,_)
  | CP.EqMin (e1,e2,e3,_)
    -> (match (is_list_exp e1) with
        | Some true -> Some true
        | _ -> (match (is_list_exp e2) with
            | Some true -> Some true
            | _ -> is_list_exp e3))
  | CP.BagIn (_,e,_) 
  | CP.BagNotIn (_,e,_)
    -> is_list_exp e
  | CP.ListIn _ 
  | CP.ListNotIn _
  | CP.ListAllN _ 
  | CP.ListPerm _
    -> Some true
  | _ -> Some false

let is_array_constraint (e: CP.formula) : bool =
  let or_list = List.fold_left (||) false in
  CP.fold_formula e (nonef, is_array_b_formula, is_array_exp) or_list

let is_array_constraint e =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "is_array_constraint" pr string_of_bool is_array_constraint e
;;

let is_relation_b_formula (pf,_) = match pf with
  | CP.ImmRel _
  | CP.RelForm _ -> Some true
  | _ -> Some false

let is_relation_constraint (e: CP.formula) : bool =
  let or_list = List.fold_left (||) false in
  CP.fold_formula e (nonef, is_relation_b_formula, nonef) or_list

let is_list_constraint (e: CP.formula) : bool =

  let or_list = List.fold_left (||) false in
  CP.fold_formula e (nonef, is_list_b_formula, is_list_exp) or_list

let is_list_constraint (e: CP.formula) : bool =
  (*Debug.no_1_opt "is_list_constraint" Cprinter.string_of_pure_formula string_of_bool (fun r -> not(r)) is_list_constraint e*)
  Debug.no_1 "is_list_constraint" Cprinter.string_of_pure_formula string_of_bool is_list_constraint e

let rec is_memo_list_constraint (f:memo_pure): bool = 
  List.exists (fun c-> 
      (List.exists is_list_constraint c.memo_group_slice)|| 
      (List.exists (fun c-> match is_list_b_formula c.memo_formula with | Some b-> b| _ -> false) c.memo_group_cons)
    ) f  

let is_mix_bag_constraint f = match f with
  | MCP.MemoF f -> is_memo_bag_constraint f
  | MCP.OnePF f -> is_bag_constraint f

let is_mix_list_constraint f = match f with
  | MCP.MemoF f -> is_memo_list_constraint f
  | MCP.OnePF f -> is_list_constraint f  

let elim_exists (f : CP.formula) : CP.formula =
  let ef = if !elim_exists_flag then CP.elim_exists f else f in
  ef

let elim_exists (f : CP.formula) : CP.formula =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "elim_exists" pr pr elim_exists f


let comm_null a1 a2 =
  let f1 = is_null a1 in
  let f2 = is_null a2 in
  if f1 && f2 then (false,a1,a2)
  else if f1 then (f1,a2,a1)
  else (f2,a1,a2)

let comm_inf a1 a2 =
  let f1 = is_inf a1 in
  let f2 = is_inf a2 in
  if f1 && f2 then (false,a1,a2)
  else if f1 then (f1,a2,a1)
  else (f2,a1,a2)

let stack_imm_add e l =
  let sv = 
    try
      (*  below returns the sum operands *)
      let sum_op add_exp = Immutils.get_imm_var_cts_operands add_exp in
      let sum_op_e = sum_op e in
      let same_sum x = Gen.BList.list_setequal_eq CP.eq_spec_var sum_op_e (sum_op x)  in
      fst (List.find ( fun (_,e0) -> same_sum e0) (imm_stk # get_stk))
    with Not_found ->
      let fresh_sv = CP.fresh_spec_var_ann ~old_name:"imm_add" ()  in
      let subs = (fresh_sv, e) in
      let _ = imm_stk # push subs in
      fresh_sv in
  CP.mkVar sv l

let replace_imm_var_with_exp sv =
  try
    let exp = snd ( imm_stk # find (fun (a,b) -> CP.eq_spec_var a sv)) in (* (sv, dummy_exp) *)
    Some exp
  with Not_found -> None

let cnv_imm_to_int_exp e =
  match e with
  | AConst (a,l)  -> Some (IConst(int_of_heap_ann a, l))
  | Add (a1,a2,l) -> 
    if CP.is_ann_type (CP.get_exp_type e) then 
      let new_var = stack_imm_add e l in
      Some new_var 
    else None
  | _ -> None

let cnv_imm_to_int_exp e =
  let pr = !CP.print_exp in
  Debug.no_1 "cnv_imm_to_int_exp" pr (pr_opt pr) cnv_imm_to_int_exp e

let transform_imm_to_int_exp_opt e =
  CP.transform_exp (x_add_1 cnv_imm_to_int_exp) e

let cnv_imm_to_int_p_formula pf lbl =
  match pf with
  | SubAnn (a1, a2, ll)-> Some (Lte (transform_imm_to_int_exp_opt a1, transform_imm_to_int_exp_opt a2, ll), lbl)
  | _ -> None

(*
  strong
  ======
  x=null  --> x=0
  x!=null --> x>0

  weak
  ====
  x=null  --> x<=0
  x!=null --> x>0  (to avoid inequality)

  bv  --> 1<=bv
*)
let cnv_ptr_to_int (ex_flag,st_flag) f = 
  let f = x_add_1 (fun f ->
    (* a=min(b,c) & some subtyping *)
    let f_0 = Immutils.prune_eq_min_max_imm f in
    (* a=min(b,c) --> (... | ...) *)
    let f_1 = Immutils.simplify_imm_min_max f_0 in
    (* a=top & a <: b & a != b *)
    let f_2 = Immutils.prune_eq_top_bot_imm f_1 in
    f_2) f in
  let f_f arg e = None in
  let f_bf (ex_flag,st_flag) bf = 
    let (pf, l) = bf in
    (* let pf = cnv_imm_to_int_p_formula pf in *)
    match pf with
    | BVar (v, ll)  ->  Some (Lte(IConst(1,ll),Var(v,ll),ll),l)
    | Eq (a1, a2, ll) -> 
      let (is_null_flag,a1,a2) = comm_null a1 a2 in
      if is_null_flag then
        if st_flag (*strengthen *) then
          Some (Eq(a1,IConst(0,ll),ll),l)
        else Some (Lte(a1,IConst(0,ll),ll),l)
        (* else let (is_inf_flag,a1,a2) = comm_inf a1 a2 in
           if is_inf_flag then
           if st_flag (*strengthen *) then
             Some (Eq(a1,mkInfConst ll,ll),l)
           else Some (Lte(a1,mkInfConst ll,ll),l)*)
      else None
    | Neq (a1, a2, ll) -> 
      let (is_null_flag,a1,a2) = comm_null a1 a2 in
      if is_null_flag then
        if st_flag (*strengthen *) then
          Some (Gt(a1,IConst(0,ll),ll),l)
        else 
          Some (Neq(a1,IConst(0,ll),ll),l)
          (*else  let (is_inf_flag,a1,a2) = comm_inf a1 a2 in
            if is_inf_flag then
              Some (Lt(a1,CP.Var(CP.SpecVar(Int,constinfinity,Unprimed),ll),ll),l)*)
      else None (* Some(bf) *)
    (* | Lte(a1,a2,ll) -> if is_inf a1 && not(is_inf a2) then Some(BConst(false,ll),l)  
       else if is_inf a2 && not(is_inf a1) then Some(BConst(true,ll),l) 
       else Some(bf)*)
    (* | Lte _ -> Some (pf,l) *)
    | _ -> cnv_imm_to_int_p_formula pf l (* None *) (* Some(bf) *)
  in
  (* let f_e arg e = (Some (cnv_imm_to_int_exp e)) in *)
  let f_e arg e = (x_add_1 cnv_imm_to_int_exp e) in
  let a_f ((ex_flag,st_flag) as flag) f =
    match f with
    | Not _ -> (not(ex_flag),not(st_flag))
    | Forall _ -> 
      if ex_flag then (false,not(st_flag))
      else flag
    | Exists _ -> 
      if ex_flag then flag
      else (true,not(st_flag))
    | _ -> flag
  in
  let a_bf a _ = a in
  let a_e a _ = a in
  map_formula_arg f (ex_flag,st_flag) (f_f, f_bf, f_e) (a_f, a_bf, a_e) 

let cnv_ptr_to_int flag f = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "cnv_ptr_to_int" (pr_pair string_of_bool string_of_bool) pr pr (fun _ _ -> cnv_ptr_to_int flag f) flag f

(*
x=0 --> x=null
x<=0 --> x=null
x<1
x>0  --> x!=null
x>=1
x>=0 --> true
x>-1
x<0  --> false
x<=-1
*)

let comm_is_null a1 a2 =
  match a1,a2 with
  | Var(v,_),IConst(0,_) ->
    let t=type_of_spec_var v in
    (is_otype t,a1,a2)
  | IConst(0,_),Var(v,_) ->
    let t=type_of_spec_var v in
    (is_otype t,a2,a1)
  | _ -> (false,a1,a2)

let comm_is_ann a1 a2 =
  match a1,a2 with
  | Var(v,_),IConst(i,_) ->
    (is_ann_type (type_of_spec_var v),a1,i, a2)
  | IConst(i,_),Var(v,_) ->
    (is_ann_type (type_of_spec_var v),a2,i, a1)
  | Var(v,_), e  ->
    (is_ann_type (type_of_spec_var v),a1,1, a2) 
  | e, Var(v,_)->
    (is_ann_type (type_of_spec_var v),a2,1, a1) 
  | _ -> (false, a1, 0, a2)

let is_bool_ctr  a1 a2 =
  match a1,a2 with
  | Var(v,_),IConst(i,_) ->
    (* assumes v<=0 or v<1 *)
    begin
      match v with 
        SpecVar(t,i,p) -> 
        (* Void this is encoding of not(v) *)
        let neg_v = SpecVar(Void,i,p) in
        if is_btype t then Some(neg_v)
        else None
    end
  | IConst(i,_),Var(v,_) ->
    (* assumes 1<=v or 0<v *)
    begin
      match v with 
        SpecVar(t,i,p) -> 
        (* Void this is encoding of not(v) *)
        (* let neg_v = SpecVar(Void,i,p) in *)
        if is_btype t then Some(v)
        else None
    end
  | _ -> None

let is_bool_eq_ctr ?(eq=true)  a1 a2 =
  match a1,a2 with
  | Var(v,_),IConst(i,_) | IConst(i,_),Var(v,_)  ->
    (* assumes v=0 : false; v!=0 : true *)
    begin
      match v with 
        SpecVar(t,id,p) -> 
        (* let t=type_of_spec_var v in *)
        (* Void this is encoding of not(v) *)
        let neg_v = SpecVar(Void,id,p) in
        if (is_btype t) then 
          if eq then if i=0 then Some(neg_v) else Some(v)
          else if i=0 then Some(v) else Some(neg_v) 
        else None
    end
  | _ -> None

let is_ptr_ctr a1 a2 =
  if (Globals.infer_const_obj # is_ana_ni) then (false,false)
  else
    match a1,a2 with
    | Var(v,_),_ ->
      let t=type_of_spec_var v in
      (is_otype t,is_ann_type t)
    | _,Var(v,_) ->
      let t=type_of_spec_var v in
      (is_otype t,is_ann_type t)
    | _ -> (false,false)

let is_ptr_ctr a1 a2 =
  let pr = Cprinter.string_of_formula_exp in
  let pb = string_of_bool in
  Debug.no_2 "is_ptr_ctr" pr pr
    (pr_pair (add_str "ptr" pb) (add_str "ann" pb)) is_ptr_ctr a1 a2

let is_valid_ann v = (int_of_heap_ann imm_bot)<=v && v<=(int_of_heap_ann imm_top)

let is_null a1 a2 =
  match a1,a2 with
  | Var(v,_),IConst(0,_) ->
    (is_otype (type_of_spec_var v),a1,a2)
  | _ -> (false,a1,a2)

let trans_int_to_imm_exp a = 
  let f_e a = 
    match a with 
    | IConst (i,loc) -> Some (Immutils.int_imm_to_exp i loc)
    | Var (sv,loc)   -> replace_imm_var_with_exp sv
    | _ -> None in
  CP.transform_exp f_e a

let f_e_trans_int_to_imm_exp a =
  match a with 
  | Var (sv,loc)   -> if (is_ann_type ((type_of_spec_var sv))) then replace_imm_var_with_exp sv else Some a
  | _ -> None

let trans_int_to_imm_exp a = 
  let pr = Cprinter.string_of_formula_exp in
  Debug.no_1 "trans_int_to_imm_exp"  pr pr trans_int_to_imm_exp a

(* Andreea : use a flag to determine aggressive simplification *)
let change_to_imm_rel_p_formula pf = 
  let f_e e = trans_int_to_imm_exp e in 
  match pf with 
  | Lte((Var(v,_) as a1), IConst(i,_),ll)  
  | Gte(IConst(i,_), (Var(v,_) as a1), ll) -> 
    if is_ann_type (type_of_spec_var v) then
      let a1 = f_e a1 in
      let new_f =
        if i<(int_of_heap_ann imm_bot)  then BConst(false, ll)
        else if (i>=(int_of_heap_ann imm_top) && !Globals.aggressive_imm_simpl) then BConst(true, ll)
        else if i=(int_of_heap_ann imm_bot) then Eq(a1, Immutils.int_imm_to_exp i ll, ll)
        else SubAnn(a1, Immutils.int_imm_to_exp i ll, ll)
      in Some new_f
    else None
  | Lte(IConst(i,_),(Var(v,_) as a1),ll) 
  | Gte((Var(v,_) as a1),IConst(i,_), ll) -> 
    if is_ann_type (type_of_spec_var v) then
      let a1 = f_e a1 in
      let new_f =
        if (i<=(int_of_heap_ann imm_bot)&& !Globals.aggressive_imm_simpl)  then BConst(true, ll)
        else if i>(int_of_heap_ann imm_top) then BConst(false, ll)
        else if i=(int_of_heap_ann imm_top) then Eq(a1, Immutils.int_imm_to_exp i ll, ll)
        else SubAnn(Immutils.int_imm_to_exp i ll, a1, ll)
      in Some new_f
    else None
  | Lte((Var(v1,_) as a1), (Var(v2,_) as a2), ll)
  | Gte((Var(v2,_) as a2), (Var(v1,_) as a1), ll) ->
    if is_ann_type (type_of_spec_var v1) && is_ann_type(type_of_spec_var v2) then Some (SubAnn(f_e a1, f_e a2, ll))
    else None
  | Eq (a1, a2, ll) -> 
    let (is_imm,a1,i,a2) = comm_is_ann a1 a2 in
    if is_imm then 
      let a1,a2 = f_e a1, f_e a2 in Some (Eq (a1,a2, ll))
    else None
  | Neq (a1, a2, ll) -> 
    let (is_imm,a1,i,a2) = comm_is_ann a1 a2 in
    if is_imm then 
      let a1,a2 = f_e a1, f_e a2 in Some (Neq (a1, a2, ll))
    else None
  | _ -> None

let change_to_imm_rel_p_formula pf = 
  let pr = !CP.print_p_formula in
  Debug.no_1 "change_to_imm_rel_p_formula" pr (pr_opt pr) change_to_imm_rel_p_formula pf

let change_to_imm_rel_p_formula pf = 
  if not (!Globals.int2imm_conv) then 
    let () = x_ninfo_pp  "conversion of int to imm is disabled"  no_pos in
    None (* disable conversion of an arith formula back to one containing imm *) 
  else change_to_imm_rel_p_formula pf 

let change_to_imm_rel_b_formula pf l = map_opt_def None (fun x -> Some (x,l)) (change_to_imm_rel_p_formula pf)

let change_to_imm_rel pf = map_opt_def pf (fun x -> x) (change_to_imm_rel_p_formula pf)

(* s>0 -> 0<s -> 1<=s *)
let to_ptr ptr_flag pf =
  let norm0 pf = match pf with
    | Gt(a,b,ll) -> Lt(CP.norm_exp b, CP.norm_exp a,ll)
    | Gte(a,b,ll) -> Lte(CP.norm_exp b, CP.norm_exp a,ll)
    | Lte(a,b,ll) -> Lte(CP.norm_exp a, CP.norm_exp b,ll)
    | Lt(a,b,ll) -> Lt(CP.norm_exp a, CP.norm_exp b,ll)
    | _ -> pf in
  let rec norm pf =
    match pf with
    | Lt(a,IConst(i,l),ll) -> norm(Lte(a,IConst(i-1,l),ll))
    | Lt(IConst(i,l),a,ll) -> norm(Lte(IConst(i+1,l),a,ll))
    | Lte((Var(v,_) as a1), IConst(i,_),ll) ->
      if ptr_flag then
        if i<=(-1) then BConst(false,ll)   (* v<=0 --> v=M; v<=1 --> @L<:v *)
        else if i>0 then BConst(true,ll)
        else Eq(a1,Null ll,ll)
      else (* ann_flag *)  change_to_imm_rel pf 
    | Lte(IConst(i,_),(Var(v,_) as a1),ll) ->
      if ptr_flag then
        if i>=1 then Neq(a1,Null ll,ll)
        else BConst(true,ll)
      else (* ann_flag *) change_to_imm_rel pf 
    | Lte(Var(_,_),Var(_,_),ll) ->  change_to_imm_rel pf
    | _ -> change_to_imm_rel pf 
  in norm (norm0 pf)

let to_ptr ptr_flag pf =
  let pr f = Cprinter.string_of_b_formula (f,None) in
  Debug.no_1 "to_ptr" pr pr (to_ptr ptr_flag)  pf


let rec cnv_int_to_ptr f = 
  let f_bf bf = 
    let (pf, l) = bf in
    match pf with
    | Eq (a1, a2, ll) -> 
      let (is_null_flag,a1,a2) = comm_is_null a1 a2 in
      if is_null_flag then
        Some(Eq(a1,Null ll,ll),l)
        (* else if bool_flag then *)
        (*   Some(CP.mkNot (BVar(a1,ll).l) None ll) *)
      else 
        begin
          match (is_bool_eq_ctr a1 a2) with
          | Some(vv) -> 
            let bv = BVar(vv,ll),l in Some(bv)
          | None ->
            let ptr_flag,ann_flag = is_ptr_ctr a1 a2 in
            if (ptr_flag || ann_flag) then Some(x_add to_ptr is_null_flag pf,l)
            (* let (is_ann_flag,_,_,_) = comm_is_ann a1 a2 in *)
            (* if is_ann_flag then  Some(x_add to_ptr is_null_flag pf,l) *)
            (* map_opt_def (Some bf) (fun x -> Some (x,l))
               (change_to_imm_rel_p_formula pf) *)
            else Some bf
        end
    | Neq (a1, a2, ll) -> 
      let (is_null_flag,a1,a2) = comm_is_null a1 a2 in
      if is_null_flag then
        Some(Neq(a1,Null ll,ll),l)
      else
        begin
          match (is_bool_eq_ctr ~eq:false a1 a2) with
          | Some(vv) -> 
            let bv = BVar(vv,ll),l in Some(bv)
          | None ->
            let ptr_flag,ann_flag = is_ptr_ctr a1 a2 in
            if (ptr_flag || ann_flag) then   Some(x_add to_ptr is_null_flag pf,l)
            (* let (is_ann_flag,_,_,_) = comm_is_ann a1 a2 in *)
            (* if is_ann_flag then Some(x_add to_ptr is_null_flag pf,l) *)
            (* map_opt_def (Some bf) (fun x -> Some (x,l)) (change_to_imm_rel_p_formula pf) *)
            else Some bf
        end
    | Gt(a2,a1,ll) | Lt(a1,a2,ll) ->
      begin
        match (is_bool_ctr a1 a2) with
        | Some(vv) -> 
            let bv = BVar(vv,ll),l in Some(bv)
        | None ->
          let ptr_flag,ann_flag = is_ptr_ctr a1 a2 in
          if ptr_flag || ann_flag then Some(x_add to_ptr ptr_flag pf,l)
          (*else if CP.is_inf a2 then Some(Neq(a1,mkInfConst ll,ll),l)*)
          else Some bf
      end
    | Lte (a1, a2,ll) | Gte(a2,a1,ll) ->
      begin
        match (is_bool_ctr a1 a2) with
        | Some(vv) -> 
            let bv = BVar(vv,ll),l in Some(bv)
        | None ->
          let ptr_flag,ann_flag = is_ptr_ctr a1 a2 in
          if ptr_flag || ann_flag then Some(x_add to_ptr ptr_flag pf,l)
          else Some bf
      end
    | _ -> Some bf
  in
  let f_f e = match e with
    | BForm (bf,l) -> 
      let res = f_bf bf in
      begin
        match res with
        | Some ((BVar(SpecVar(t,id,p1),p2),ll) as ans) ->
          if t==Void then 
            Some (mkNot (BForm ((BVar(SpecVar(Bool,id,p1),p2),ll),l)) None p2)
          else Some (BForm(ans,l))
        | Some(nb) -> Some(BForm(nb,l))
        | None -> Some(e)
      end
    | _ -> None 
    (* | Lte ((Var(v,_) as a1), IConst(0,_), ll) | Gte (IConst(0,_), (Var(v,_) as a1), ll)  *)
    (* | Lt ((Var(v,_) as a1), IConst(1,_), ll) | Gt (IConst(1,_), (Var(v,_) as a1), ll) ->  *)
    (*     if is_otype (type_of_spec_var v) then *)
    (*         Some(Eq(a1,Null ll,ll),l) *)
    (*     else Some bf *)
    (* | Gte ((Var(v,_) as a1), IConst(1,_), ll) | Lte (IConst(1,_), (Var(v,_) as a1), ll)   *)
    (* | Gt ((Var(v,_) as a1), IConst(0,_), ll) | Lt (IConst(0,_), (Var(v,_) as a1), ll) -> *)
    (*       if is_otype (type_of_spec_var v) then *)
    (*         Some(Neq(a1,Null ll,ll),l) *)
    (*       else Some bf *)
    (* | Gte (Var(v,_), IConst(0,_), ll) | Lte (IConst(0,_), Var(v,_), ll) ->  *)
    (* if is_otype (type_of_spec_var v) then *)
    (*         Some(BConst(true,ll),l) *)
    (* else Some bf *)
    (* | Lt (Var(v,_), IConst(0,_), ll) | Gt (IConst(0,_), Var(v,_), ll) ->  *)
    (*     if is_otype (type_of_spec_var v) then *)
    (* Some (BConst(false,ll),l) *)
    (*     else Some bf *)
  in
  let f_e e = (Some e) in
  map_formula f (f_f, f_bf, f_e) 

let cnv_int_to_ptr f = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "cnv_int_to_ptr" pr pr (fun _ -> cnv_int_to_ptr f) f

(* let ex22 =  CP.norm_exp ex2 in *)

(* this is to normalize result from simplify/hull/gist *)
let norm_pure_result f =
  let f = x_add_1 cnv_int_to_ptr f in
  let f = if !Globals.allow_inf (*&& not(!Globals.allow_inf_qe_coq)*)
    then let f =  (*CP.arith_simplify 13*) (Infinity.convert_var_to_inf f) in
      let drop_inf_constr f =   
        let f_f e = None in
        let f_bf bf = 
          let (pf, l) = bf in
          match pf with
          | Lt(a1,a2,pos) -> if Infinity.check_neg_inf2_inf a1 a2 || Infinity.check_neg_inf2_inf a2 a1
            then Some(mkTrue_b pos) else Some bf
          | Lte(e1,e2,pos) -> (match e1 with
              | Add(a1,a2,pos) -> (match a1,a2 with
                  | IConst(1,_), e 
                  | e,IConst(1,_) ->  if is_inf e then Some(Lt(e,e2,pos),None) else Some bf
                  | _, _ -> Some bf)
              | _ -> Some bf)
          | _ -> Some bf
        in
        let f_e e = (Some e) in
        map_formula f (f_f, f_bf, f_e) in 
      let f = drop_inf_constr f in
      Infinity.normalize_inf_formula f
    else f in 
  let f = if !Globals.allow_norm_disj then NM.norm_disj f else f in
  let () = imm_stk # reset in
  (* Omega.trans_bool *) f

let norm_pure_result f =
  let pr = Cprinter.string_of_pure_formula in
  let pr2 s = s # string_of in
  Debug.no_2 "norm_pure_result" pr pr2 pr (fun _ _  -> norm_pure_result f) f imm_stk

let wrap_pre_post_gen pre post f a =
  let s1 = pre a in
  let r2 = f a in
  let res =  post s1 r2 in
  res

let wrap_pre_post_print s fn x =
  let pr = Cprinter.string_of_pure_formula in
  let pre f = 
    if !Globals.print_cnv_null then pr f
    else "" in 
  let post s1 r2 = 
    if !Globals.print_cnv_null 
    then 
      let s2 = pr r2 in
      (* if String.compare s1 s2 == 0 then r2 *)
      (* else  *)
      begin
        print_endline_quiet s;
        print_endline_quiet ("input :"^s1);
        print_endline_quiet ("output:"^s2);
        r2
      end
    else r2
  in wrap_pre_post_gen pre post (fun _ -> fn x) x


let add_imm_inv f1 f2 = 
  (* find immutability vars *)
  (* form a list of imm_inv to add *)
  let vs = fv (mkAnd f1 f2 no_pos) in
  let vs = List.filter (fun v -> CP.is_ann_type (CP.type_of_spec_var v)) vs in
  let vs = CP.remove_dups_svl vs in
  let inv = List.map (fun v -> 
      let vp=Var(v,no_pos) in 
      mkAnd (mkSubAnn const_ann_bot vp) (mkSubAnn vp const_ann_top) no_pos ) vs in
  let f1_inv = join_conjunctions (f1::inv) in
  let () = x_tinfo_hp (add_str "Ann Vars" Cprinter.string_of_spec_var_list) vs no_pos in
  let () = x_tinfo_hp (add_str "Inv" Cprinter.string_of_pure_formula) f1_inv no_pos in
  f1_inv

let add_imm_inv f1 f2 =
  let pr = Cprinter.string_of_pure_formula in
 Debug.no_2 "add_imm_inv" pr pr pr add_imm_inv f1 f2

let cnv_ptr_to_int_weak f =
  wrap_pre_post_print "cnv_ptr_to_int_weak" (x_add cnv_ptr_to_int (true,false)) f

let cnv_ptr_to_int(* _strong *) f =
  wrap_pre_post_print "cnv_ptr_to_int" (x_add cnv_ptr_to_int (true,true)) f

let cnv_ptr_to_int f = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "cnv_ptr_to_int#2" pr pr cnv_ptr_to_int f

let norm_pure_result f =
  wrap_pre_post_print "norm_pure_result" norm_pure_result f


(* let cnv_ptr_to_int f = *)
(*   let pr = Cprinter.string_of_pure_formula in *)
(*    Debug.no_1 "cnv_ptr_to_int" pr pr cnv_ptr_to_int f *)

(* let cnv_int_to_ptr f =  *)
(*   let pr = Cprinter.string_of_pure_formula in *)
(*   let pre f =  *)
(*     if !Globals.print_cnv_null then pr f *)
(*     else "" in  *)
(*   let post s1 r2 =  *)
(*     if !Globals.print_cnv_null  *)
(*     then  *)
(*       let s2 = pr r2 in *)
(*       if String.compare s1 s2 == 0 then r2 *)
(*       else  *)
(*         begin *)
(*           print_endline "cnv_int_to_ptr"; *)
(*           print_endline ("input :"^s1); *)
(*           print_endline ("output:"^s2); *)
(*           r2 *)
(*         end *)
(*     else r2 *)
(*   in wrap_pre_post_gen pre post (fun _ -> cnv_int_to_ptr f true) f *)

(* let cnv_int_to_ptr f = *)
(*   let pr = Cprinter.string_of_pure_formula in *)
(*   Debug.no_1 "cnv_int_to_ptr" pr pr cnv_int_to_ptr f *)

let wrap_pre_post pre post f a =
  let a = pre a in
  let r = f a in
  let res = post r in
  res

(*  
   [["a","b"]:f1; "a":f2; "b":f3; "c":f4]

   ==> build_compatible_sets

   [["a","b"]:f1 & f2 & f3; "a":f2; "b":f3; "c":f4]

   ==> elim_subsumption

   [["a","b"]:f1 & f2 & f3; "c":f4]

*)
let build_labels_sat is_comp lbs = 
  (* let lbs = List.sort LO.compare lbs in *)
  let res = List.map (fun l1 -> (l1,List.filter (is_comp l1) lbs)) lbs in
  let res = List.sort (fun (_,l1) (_,l2) -> 
      let n1=List.length l1 in
      let n2=List.length l2 in
      if n1==n2 then 0
      else if n1<n2 then 1
      else -1
    ) res in
  res 

let build_labels_sat is_comp lbs = 
  let pr1 = pr_list_semi LO.string_of in
  let pr2 = pr_list (pr_pair LO.string_of pr1) in
  Debug.no_1 "build_labels_sat" pr1 pr2 (build_labels_sat is_comp) lbs

let merge_lbls used labs =
  let flag = ref false in
  let rec aux aa bb =
    match aa,bb with
    | [],[] -> []
    | [],_ -> (flag:=true; bb)
    | _,[] -> aa
    | (x::xs),y::ys -> 
      let r = LO.compare x y in
      if r<0 then x::(aux xs bb)
      else if r=0 then x::(aux xs ys)
      else (flag:=true; y::(aux aa ys))
  in
  let res = aux used labs in
  (res,!flag)

let merge_lbls used labs =
  let pr1 = pr_list_semi LO.string_of in
  (* let pr2 = pr_list (pr_pair LO.string_of pr1) in *)
  Debug.no_2 "merge_lbls"  pr1 pr1 (pr_pair pr1 string_of_bool) merge_lbls used labs

let prune_labels_sat lbs =
  let rec aux used lbs =
    match lbs with
    | [] -> []
    | ((_,ls) as xs)::rest ->
      let (new_used,flag) = merge_lbls used ls in
      if List.length new_used > List.length used 
      then xs::(aux new_used rest)
      else aux new_used rest
  in aux [] lbs 

let prune_labels_sat lbs =
  let pr1 = pr_list_semi LO.string_of in
  let pr2 = pr_list (pr_pair LO.string_of pr1) in
  Debug.no_1 "prune_labels_sat" pr2 pr2 (prune_labels_sat) lbs

let build_branches_sat br lbs = 
  let nlbs = prune_labels_sat lbs in
  let mbr = List.map (fun (l,ls) -> 
      let nf = List.filter (fun (l2,f) -> List.mem l2 ls) br in
      let nf = List.fold_left (fun a (_,f) -> mkAnd a f no_pos) (mkTrue no_pos) nf in
      (l,nf)) nlbs in
  mbr

let build_branches_sat br lbs = 
  let pr1 = pr_list_semi LO.string_of in
  let pr2 = pr_list (pr_pair LO.string_of pr1) in
  let pr3 = pr_list (pr_pair LO.string_of !print_formula) in
  Debug.no_2 "build_branches_sat" (add_str "br" pr3) (add_str "lbs" pr2) pr3 (build_branches_sat) br lbs

let sat_label_filter fct f =
  let pr = Cprinter.string_of_pure_formula in
  let test f1 = 
    if no_andl f1 then  fct f1 
    else report_error no_pos ("unexpected imbricated AndList in tpdispatcher sat: "^(pr f)) in
  let rec helper_x f = match f with 
    | AndList b -> 
      let lbls = Label_Pure.get_labels b in
      (* Andreea : this is to pick equality from all branches *)
      let (comp,fil) = 
        if !Globals.label_aggressive_sat
        then (LO.is_fully_compatible_sat,fun fs -> fs)
        else (LO.is_part_compatible_sat,
              List.filter (fun (l,_)-> not(LO.is_common l)) ) 
      in
      let b = 
        if !Globals.label_aggressive_sat
        then extract_eset_of_lbl_lst b []
        (* extract_eq_clauses_lbl_lst b *)
        else b 
      in
      let sat_lbls = build_labels_sat (fun x y -> comp y x) lbls in
      let sat_branches = build_branches_sat b sat_lbls in
      (* let fs = List.map (fun l ->  *)
      (*     let lst = List.filter (fun (c,_)-> comp c l) b in *)
      (*     (l,List.fold_left (fun a c-> mkAnd a (snd c) no_pos) (mkTrue no_pos) lst)) lbls in *)
      (* let () = Debug.ninfo_hprint (add_str "fs" Label_Pure.string_of) fs no_pos in *)
      (* (\* let fs2 = List.filter (fun (l,_)-> l!=[]) fs in *\) *)
      (* let fs2 = fil fs in *)
      (* let fs = if fs2==[] then fs else fs2 in *)
      let fs = sat_branches in
      let () = Debug.ninfo_hprint (add_str "label,fs" (pr_list (pr_pair (pr_list pr_id) pr)))  fs no_pos in
      let res = List.exists (fun (_,f) -> (test f)=false) fs in
      not(res)
    | Or (f1,f2,_ ,_)-> (helper f1)||(helper f2)
    | _ -> test f 
  and helper f = Debug.no_1(* _loop *) "sat_label_filter_helper"  !print_formula string_of_bool helper_x f in
  helper f

let sat_label_filter fct f = 
  Gen.Profiling.do_1 "sat_label_filter" (sat_label_filter fct) f

let sat_label_filter fct f =  Debug.no_1 "sat_label_filter" !print_formula string_of_bool (fun _ -> sat_label_filter fct f) f

let imply_label_filter ante conseq = 
  (*let s = "unexpected imbricated AndList in tpdispatcher impl: "^(Cprinter.string_of_pure_formula ante)^"|-"^(Cprinter.string_of_pure_formula conseq)^"\n" in*)
  let comp = 
    if  !Globals.label_aggressive_imply
    then LO.is_fully_compatible_imply
    else LO.is_part_compatible_imply
  in
  match ante,conseq with
  | Or _,_  
  | _ , Or _ -> [(andl_to_and ante, andl_to_and conseq)]
  | AndList ba, AndList bc -> 
    (* let fc = List.for_all (fun (_,c)-> no_andl c) in *)
    (*   (if fc ba && fc bc then () else print_string s; *)
    let ba = 
      if !Globals.label_aggressive_imply
      then extract_eset_of_lbl_lst ba bc
      else ba
    in
    List.map (fun (lconseq, fconseq)-> 
        let lst = List.filter (fun (lante,_)-> comp (* LO.is_part_compatible *) lante lconseq) ba in 
        let fs_ante = List.fold_left (fun a (_,c)-> mkAnd a c no_pos) (mkTrue no_pos) lst in
        (*(andl_to_and fr1, andl_to_and c)*)
        (fs_ante,fconseq)) bc
  | AndList ba, _ -> [(andl_to_and ante,conseq)]
  (*if (List.for_all (fun (_,c)-> no_andl c) ba)&& no_andl conseq then () else print_string s;*)
  | _ , AndList bc -> List.map (fun (_,c)-> (ante,c)) bc 
  | _ -> [ante,conseq]
(*if (no_andl ante && no_andl conseq) then [ante,conseq]
  	      else 
  	      (print_string s;
  	      [(andl_to_and ante),(andl_to_and conseq)])*)


(*keeps labels only if both sides have labels otherwise do a smart collection.*)
(*this applies to term reasoning for example as it seems the termination annotations loose the labels...*)
let imply_label_filter ante conseq = 
  let pr = !print_formula in
  Debug.no_2 "imply_label_filter" pr pr (pr_list (pr_pair pr pr)) imply_label_filter ante conseq

let assumption_filter_slicing (ante : CP.formula) (cons : CP.formula) : (CP.formula * CP.formula) =
  let overlap (nlv1, lv1) (nlv2, lv2) =
    if (nlv1 = [] && nlv2 = []) then (Gen.BList.list_equiv_eq CP.eq_spec_var lv1 lv2)
    else (Gen.BList.overlap_eq CP.eq_spec_var nlv1 nlv2) && (Gen.BList.list_equiv_eq CP.eq_spec_var lv1 lv2)
  in

  let rec group_conj l = match l with
    | [] -> (false,[]) 
    | ((f_nlv, f_lv), fs)::t ->  
      let b,l = group_conj t in
      let l1, l2 = List.partition (fun (cfv, _) -> overlap (f_nlv, f_lv) cfv) l in
      if l1==[] then (b,((f_nlv, f_lv), fs)::l) 
      else 
        let l_fv, nfs = List.split l1 in
        let l_nlv, l_lv = List.split l_fv in
        let nfs = CP.join_conjunctions (fs::nfs) in
        let n_nlv = CP.remove_dups_svl (List.concat (f_nlv::l_nlv)) in
        let n_lv = CP.remove_dups_svl (List.concat (f_lv::l_lv)) in
        (true,((n_nlv, n_lv), nfs)::l2)
  in

  let rec fix n_l = 
    let r1, r2 = group_conj n_l in
    if r1 then fix r2 else r2
  in    

  let split_sub_f f = 
    let conj_list = CP.split_conjunctions f in
    let n_l = List.map
        (fun c -> (CP.fv_with_slicing_label c, c)) conj_list in
    snd (List.split (fix n_l))
  in

  let pick_rel_constraints cons ante =
    let fv = CP.fv cons in
    let rec exhaustive_collect_with_selection fv ante =
      let (n_fv, n_ante1, r_ante) = List.fold_left (
          fun (afv, ac, rc) f ->
            let f_ulv, f_lv = CP.fv_with_slicing_label f in
            let cond_direct = Gen.BList.overlap_eq CP.eq_spec_var afv f_ulv in
            let cond_link = (f_ulv = []) && (Gen.BList.subset_eq CP.eq_spec_var f_lv afv) in
            if (cond_direct || cond_link) then
              (afv@(CP.fv f), ac@[f], rc)
            else (afv, ac, rc@[f])
        ) (fv, [], []) ante
      in
      if n_fv = fv then n_ante1
      else
        let n_ante2 = exhaustive_collect_with_selection n_fv r_ante in
        n_ante1 @ n_ante2
    in
    exhaustive_collect_with_selection fv ante
  in

  let ante = CP.elim_exists(*_with_fresh_vars*) ante in

  let l_ante = split_sub_f ante in

  (*let () = print_string ("imply_timeout: filter: l_ante:\n" ^
    (List.fold_left (fun acc f -> acc ^ "+++++++++\n" ^ (Cprinter.string_of_pure_formula f) ^ "\n") "" l_ante)) in*)

  (CP.join_conjunctions (pick_rel_constraints cons l_ante), cons)

let assumption_filter (ante : CP.formula) (cons : CP.formula) : (CP.formula * CP.formula) =
  if (CP.isConstFalse cons) then (ante,cons) else
    let conseq_vars = CP.fv cons in
    if (List.exists (fun v -> CP.name_of_spec_var v = waitlevel_name) conseq_vars) then
      (ante,cons)
    else
      CP.assumption_filter ante cons

let assumption_filter (ante : CP.formula) (cons : CP.formula) : (CP.formula * CP.formula) =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "assumption_filter" pr pr (fun (l, _) -> pr l)
    assumption_filter ante cons

let norm_pure_input f =
  let f = x_add_1 cnv_ptr_to_int f in
  let f = if !Globals.allow_inf 
    then let f = Infinity.convert_inf_to_var f
      in let add_inf_constr = BForm((mkLt (CP.Var(CP.SpecVar(Int,constinfinity,Primed),no_pos)) (CP.Var(CP.SpecVar(Int,constinfinity,Unprimed),no_pos)) no_pos,None),None) in
      let f = mkAnd add_inf_constr f no_pos in f
    else f in f

let norm_pure_input f =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "norm_pure_input" pr pr norm_pure_input f 

(* rename and shorten variables for better caching of formulas *)
(* TODO WN: check if it avoids name clashes? *)
let norm_var_name (e: CP.formula) : CP.formula =
  let shorten_sv (CP.SpecVar (typ, name, prm)) vnames =
    let short_name =
      try
        Hashtbl.find vnames name
      with Not_found ->
        let fresh_name = "v" ^ (string_of_int (Hashtbl.length vnames)) in
        let () = Hashtbl.add vnames name fresh_name in
        fresh_name
    in
    CP.SpecVar (typ, short_name, prm)
  in
  let f_bf vnames bf =
    let (pf,il) = bf in
    match pf with
    | CP.BVar (sv, l) -> Some ((CP.BVar (shorten_sv sv vnames, l)), il)
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
    | CP.AndList b -> CP.AndList (map_l_snd (fun c -> simplify c vnames) b)
    | CP.Or (f1, f2, lbl, l) ->
      let nf1 = simplify f1 vnames in
      let nf2 = simplify f2 vnames in
      let r = CP.mkOr nf1 nf2 lbl l in
      r
    | CP.Not (f1, lbl, l) ->
      CP.Not (simplify f1 vnames, lbl, l)
    | CP.BForm (bf, lbl) ->
      CP.BForm (CP.map_b_formula_arg bf vnames (f_bf, f_e) (idf2, idf2), lbl)
  in
  (* renaming free vars to unique vars for better caching *)
  let simplify f0 vnames = 
    let pr = Cprinter.string_of_pure_formula in
    (* let pr_hashtbl h = Hashtbl.fold (fun d1 d2 a -> *)
    (*     ("(" ^ (pr_id  d1) ^ "; " ^ (pr_id d2) ^ ")\n")) h "" in *)
    Debug.no_1 "simplify-syn" pr (* pr_hashtbl *) pr (fun _ -> simplify f0 vnames) f0 (* vnames *)
  in
  let simplify f0 = x_add simplify f0  (Hashtbl.create 100) in
  let simplify f0 = wrap_pre_post norm_pure_input norm_pure_result simplify f0 in
  simplify e (* (Hashtbl.create 100) *)

let norm_var_name (e: CP.formula) : CP.formula =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "norm_var_name" pr pr norm_var_name e

(* Statistical function for formula size counting *)
let disj_cnt a c s =
  if (!Gen.enable_counters) then
    begin
      let rec p_f_size f = match f with
        | CP.BForm _ -> 1
        | CP.AndList b -> List.fold_left (fun a (_,c)-> a+(p_f_size c)) 0 b
        | CP.And (f1,f2,_) | CP.Or (f1,f2,_,_) -> (p_f_size f1)+(p_f_size f2)
        | CP.Not (f,_,_) | CP.Forall (_,f,_,_ ) | CP.Exists (_,f,_,_) -> p_f_size f in

      let rec or_f_size f = match f with
        | CP.BForm _ -> 1
        | CP.And (f1,f2,_) -> (or_f_size f1)*(or_f_size f2)
        | CP.AndList b -> List.fold_left (fun a (_,c)-> a*(p_f_size c)) 0 b
        | CP.Or (f1,f2,_,_) -> (or_f_size f1)+(or_f_size f2)
        | CP.Not (f,_,_) | CP.Forall (_,f,_,_ ) | CP.Exists (_,f,_,_) -> or_f_size f in
      let rec add_or_f_size f = match f with
        | CP.BForm _ -> 0
        | CP.AndList b -> List.fold_left (fun a (_,c)-> a+(p_f_size c)) 0 b
        | CP.And (f1,f2,_) -> (add_or_f_size f1)+(add_or_f_size f2)
        | CP.Or (f1,f2,_,_) -> 1+(add_or_f_size f1)+(add_or_f_size f2)
        | CP.Not (f,_,_) | CP.Forall (_,f,_,_ ) | CP.Exists (_,f,_,_) -> add_or_f_size f in
      match c with
      | None -> 
        Gen.Profiling.inc_counter ("stat_count_"^s);
        Gen.Profiling.add_to_counter ("z_stat_disj_"^s) (1+(add_or_f_size a));
        Gen.Profiling.add_to_counter ("stat_disj_count_"^s) (or_f_size a);
        Gen.Profiling.add_to_counter ("stat_size_count_"^s) (p_f_size a)
      | Some c-> 
        Gen.Profiling.inc_counter ("stat_count_"^s);
        Gen.Profiling.add_to_counter ("z_stat_disj_"^s) (1+(add_or_f_size a)); 
        Gen.Profiling.add_to_counter ("stat_disj_count_"^s) ((or_f_size a)+(or_f_size c));
        Gen.Profiling.add_to_counter ("stat_size_count_"^s) ((p_f_size a)+(p_f_size c)) ;
    end
  else ()

let tp_is_sat_no_cache (f : CP.formula) (sat_no : string) =
  if not !tp_batch_mode then start_prover ();
  (* Drop array formula *)
  (* let f = translate_array_relation f in *)
  (* let f = drop_array_formula f in *)
  let _ = CP.filter_bag_constrain f f in
  let f = CP.concretize_bag_pure f in
  let f = CP.translate_waitS_pure f in (*waitS before acyclic*)
  let f = CP.translate_acyclic_pure f in
  let f,_ = x_add CP.translate_tup2_imply f (CP.mkTrue no_pos)in
  let f = if (!Globals.allow_locklevel) then
      (*should translate waitlevel before level*)
      let f = CP.infer_level_pure f in (*add l.mu>0*)
      let f = CP.translate_waitlevel_pure f in
      let f = CP.translate_level_pure f in
      let () = x_dinfo_hp (add_str "After translate_: " Cprinter.string_of_pure_formula) f no_pos in
      f
    else
      (* let f = CP.drop_svl_pure f [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in *)
      (* let f = CP.drop_locklevel_pure f in *)
      f
  in
  (* ============================================================== *)
  (* superceded by add_imm_inv which is only done for ante of imply *)
  (* ============================================================== *)
  (* let vrs = Cpure.fv f in *)
  (* let imm_vrs = List.filter (fun x -> (CP.type_of_spec_var x) == AnnT) vrs in  *)
  (* let f = Cpure.add_ann_constraints imm_vrs f in *)
  let () = disj_cnt f None "sat_no_cache" in
  let (pr_weak,pr_strong) = CP.drop_complex_ops in
  let (pr_weak_z3,pr_strong_z3) = CP.drop_complex_ops_z3 in
  (* Handle Infinity Constraints *)
  let f = if !Globals.allow_inf then 
      (* let _ = Coqinf.cpure_to_coqpure f in *)
      let f = Infinity.normalize_inf_formula_sat f in
      let f = (*Infinity.fixed_point_pai_num*) f in f
    else f in
  let wf = f in
  let omega_is_sat f = Omega.is_sat_ops pr_weak pr_strong f sat_no in
  let redlog_is_sat f = wrap_redlog (Redlog.is_sat_ops pr_weak pr_strong f) sat_no in
  let ocredlog_is_sat f = wrap_ocredlog (Redlog.is_sat_ops pr_weak pr_strong f) sat_no in
  let mathematica_is_sat f = Mathematica.is_sat_ops pr_weak pr_strong f sat_no in
  let mona_is_sat f = Mona.is_sat_ops pr_weak pr_strong f sat_no in
  let coq_is_sat f = Coq.is_sat_ops pr_weak pr_strong f sat_no in
  let z3_is_sat f = Smtsolver.is_sat_ops pr_weak_z3 pr_strong_z3 f sat_no in
  let z3n_is_sat f = Z3.is_sat_ops_cex pr_weak_z3 pr_strong_z3 f sat_no in

  (* let () = Gen.Profiling.push_time "tp_is_sat" in *)
  let f = x_add_1 Cpure.subs_const_var_formula f in
  let res = (
    match !pure_tp with
    | DP -> 
      let r = Dp.is_sat f sat_no in
      if test_db then (
        (* let r2 = Smtsolver.is_sat f sat_no in *)
        let r2 = z3_is_sat f in
        if r=r2 then r
        else failwith ("dp-omega mismatch on sat: "^(Cprinter.string_of_pure_formula f)^" d:"^(string_of_bool r)^" o:"^(string_of_bool r2)^"\n")
      )
      else r
    | OmegaCalc ->
      if (CP.is_float_formula wf) then (redlog_is_sat wf)
      else (omega_is_sat f);
    | CvcLite -> Cvclite.is_sat f sat_no
    | Cvc4 -> (
        match !provers_process with
        |Some proc -> Cvc4.is_sat_increm !provers_process f sat_no
        | _ -> Cvc4.is_sat f sat_no
      )
    | Z3 -> z3_is_sat f
    | Z3N -> z3n_is_sat f
    | Isabelle -> Isabelle.is_sat wf sat_no
    | Coq ->
      if (is_list_constraint wf) then (coq_is_sat wf)
      else (Smtsolver(*Omega*).is_sat f sat_no);
    | Mona | MonaH -> mona_is_sat wf
    | CO -> (
        let result1 = (Cvc4.is_sat_helper_separate_process wf sat_no) in
        match result1 with
        | Some f -> f
        | None -> omega_count := !omega_count + 1;
          (omega_is_sat f)
      )
    | CM -> (
        if (is_bag_constraint wf) then (mona_is_sat wf)
        else
          let result1 = (Cvc4.is_sat_helper_separate_process wf sat_no) in
          match result1 with
          | Some f -> f
          | None -> omega_count := !omega_count + 1;
            (omega_is_sat f)
      )
    | OM ->
      if (is_bag_constraint wf) then (mona_is_sat wf)
      else (omega_is_sat f)
    | AUTO ->
      if (is_bag_constraint wf) then (mona_is_sat wf)
      else if (is_list_constraint wf) then (coq_is_sat wf)
      else if (is_array_constraint f) then (z3_is_sat f)
      else (omega_is_sat f)
    | OZ ->
      if (is_array_constraint f) then (z3_is_sat f)
      else (omega_is_sat f)
    | OI ->
      if (is_bag_constraint wf) then (Isabelle.is_sat wf sat_no)
      else (omega_is_sat f)
    | SetMONA -> Setmona.is_sat wf
    | Redlog -> redlog_is_sat wf
    | OCRed -> ocredlog_is_sat wf
    | Mathematica -> mathematica_is_sat wf
    | RM ->
      if (is_bag_constraint wf) && (CP.is_float_formula wf) then
        (* Mixed bag constraints and float constraints *)
        (*TO CHECK: soundness. issat(f) = issat(f1) & is(satf2)*)
        let f_no_float = CP.drop_float_formula wf in
        let f_no_bag = CP.drop_bag_formula wf in
        let () = x_dinfo_zp (lazy ("SAT #" ^ sat_no ^ " : mixed float + bag constraints ===> partitioning: \n ### " ^ (!print_pure wf) ^ "\n INTO : " ^ (!print_pure f_no_float) ^ "\n AND : " ^ (!print_pure f_no_bag) )) no_pos
        in
        let b1 = mona_is_sat f_no_float in
        let b2 = redlog_is_sat f_no_bag in
        (* let () = print_endline ("\n### b1 = " ^ (string_of_bool b1) ^ "\n ### b2 = "^ (string_of_bool b2)) in *)
        (b1 && b2)
      else
      if (is_bag_constraint wf) then
        mona_is_sat wf
      else
        redlog_is_sat wf
    | PARAHIP ->

      if (is_relation_constraint wf) && (is_bag_constraint wf) && (CP.is_float_formula wf) then
        (* Mixed bag constraints, relations and float constraints *)
        (*TO CHECK: soundness. issat(f) = issat(f1) & is(satf2)*)
        let f_no_float_rel = CP.drop_rel_formula (CP.drop_float_formula wf) in
        let f_no_bag_rel = CP.drop_rel_formula (CP.drop_bag_formula wf) in
        let f_no_float_bag = CP.drop_float_formula (CP.drop_bag_formula wf) in
        let () = x_dinfo_zp (lazy ("SAT #" ^ sat_no ^ " : mixed float + relation + bag constraints ===> partitioning: \n ### " ^ (!print_pure wf) ^ "\n INTO : " ^ (!print_pure f_no_float_rel) ^ "\n AND : " ^ (!print_pure f_no_bag_rel) ^ "\n AND : " ^ (!print_pure f_no_float_bag) )) no_pos
        in
        let b1 = mona_is_sat f_no_float_rel in
        let b2 = redlog_is_sat f_no_bag_rel in
        let b3 = z3_is_sat f_no_float_bag in
        (b1 && b2 &&b3)
      else
        (*UNSOUND - for experimental purpose only*)
      if (is_bag_constraint wf) && (CP.is_float_formula wf) then
        (* Mixed bag constraints and float constraints *)
        (*TO CHECK: soundness. issat(f) = issat(f1) & is(satf2)*)
        let f_no_float = CP.drop_float_formula wf in
        let f_no_bag = CP.drop_bag_formula wf in
        let () = x_dinfo_zp (lazy ("SAT #" ^ sat_no ^ " : mixed float + bag constraints ===> partitioning: \n ### " ^ (!print_pure wf) ^ "\n INTO : " ^ (!print_pure f_no_float) ^ "\n AND : " ^ (!print_pure f_no_bag) )) no_pos
        in
        let f_no_float_bag_only = CP.collect_all_constraints is_bag_constraint f_no_float in
        let f_no_float_no_bag = CP.drop_bag_formula f_no_float in
        let b =  z3_is_sat f_no_float_no_bag in
        let b1 = mona_is_sat f_no_float_bag_only in
        (* let b1 = mona_is_sat f_no_float in *)
        let b2 = redlog_is_sat f_no_bag in
        (* (b1 && b2) *)
        b && b1 && b2
      else
      if (is_relation_constraint wf) then
        let f = CP.drop_bag_formula (CP.drop_float_formula wf) in
        z3_is_sat f
      else if (is_bag_constraint wf ) then
        let f = CP.drop_rel_formula (CP.drop_float_formula wf) in
        let (bag_cnts, others) = List.partition is_bag_constraint (list_of_conjs f) in
        let bag_f = conj_of_list bag_cnts no_pos in
        let no_bag_f =  conj_of_list others no_pos in
        (* Approx: mona can only deal with natural numbers (non negative) *)
        (mona_is_sat bag_f && z3_is_sat no_bag_f)
      else if (is_float_formula wf ) then
        let f = CP.drop_bag_formula (CP.drop_rel_formula wf) in
        redlog_is_sat f
      else
        (* Anything else -> z3: faster *)
        z3_is_sat f
    | ZM ->
      if (is_bag_constraint wf) then mona_is_sat wf
      else z3_is_sat wf
    | SPASS -> Spass.is_sat f sat_no
    | MINISAT -> Minisat.is_sat f sat_no
    | LOG -> find_bool_proof_res sat_no
  ) in 
  if not !tp_batch_mode then stop_prover ();
  res

let tp_is_sat_no_cache (f : CP.formula) (sat_no : string) =
  let f = x_add_1 cnv_ptr_to_int f in
  let flag = tp_is_sat_no_cache f sat_no in 
  if !Globals.allow_inf && !Globals.allow_inf_qe
  then  
    (*  let exists_inf f = 
        let alist  = Infinity.quantifier_elim f in
         let rec aux al = match al with
           | [] -> false
           | x::xs -> let f = tp_is_sat_no_cache f sat_no in
                      (*let _ = print_endline ("Ante :"^(Cprinter.string_of_pure_formula x)) in*)
                      if f then true else aux xs
         in aux alist in
        let forall_lst = Infinity.get_inst_forall f in 
        let forall_lst = f::forall_lst in 
        let f = List.exists (fun c -> exists_inf c) forall_lst in f*)
    let expand_quantifier = Infinity.elim_forall_exists in
    tp_is_sat_no_cache (expand_quantifier f) sat_no
  else if !Globals.allow_inf && !Globals.allow_inf_qe_coq then
    let f  = Coqinf.check_sat_inf_formula f in
    (*let fl = CP.split_disjunctions_deep f in
      let rec aux al = match al with
      | [] -> false
      | x::xs -> if (tp_is_sat_no_cache x sat_no) then true else aux xs
      in aux fl*)
    Omega.is_sat f sat_no 
    (*tp_is_sat_no_cache f sat_no*)
  else flag 

let tp_is_sat_no_cache (f : CP.formula) (sat_no : string) = 
  Gen.Profiling.do_1 "tp_is_sat_no_cache" (tp_is_sat_no_cache f) sat_no

let tp_is_sat_no_cache (f : CP.formula) (sat_no : string) = 
  Debug.no_3 "tp_is_sat_no_cache"
    string_of_prover Cprinter.string_of_pure_formula (fun s -> s) string_of_bool
    (fun _ _ _ -> tp_is_sat_no_cache f sat_no) !pure_tp f sat_no

let tp_is_sat_perm f sat_no = 
  if !perm=Dperm then match CP.has_tscons f with
    | No_cons -> tp_is_sat_no_cache f sat_no
    | No_split	-> true
    | Can_split ->
      let tp_wrap f = if CP.isConstTrue f then true else tp_is_sat_no_cache f sat_no in
      let tp_wrap f = Debug.no_1 "tp_is_sat_perm_wrap" Cprinter.string_of_pure_formula (fun c-> "") tp_wrap f in
      let ss_wrap (e,f) = if f=[] then true else Share_prover_w2.sleek_sat_wrapper (e,f) in
      List.exists (fun f-> tp_wrap (CP.tpd_drop_perm f) && ss_wrap ([],CP.tpd_drop_nperm f)) (snd (CP.dnf_to_list f)) 
  else tp_is_sat_no_cache f sat_no

let tp_is_sat_perm f sat_no =  Debug.no_1(* _loop *) "tp_is_sat_perm" Cprinter.string_of_pure_formula string_of_bool (fun _ -> tp_is_sat_perm f sat_no) f

let cache_status = ref false 
let cache_sat_count = ref 0 
let cache_sat_miss = ref 0 
let cache_imply_count = ref 0 
let cache_imply_miss = ref 0 

let last_prover () =
  if !cache_status then "CACHED"
  else  Others.last_tp_used # string_of

let find_cache ht fstring fstring_prover =
  try
     Hashtbl.find ht fstring  (* sound generic answer *)
  with Not_found ->
     Hashtbl.find ht (fstring_prover) (* provers-specific answer *)

let sat_cache is_sat (f:CP.formula) : bool  = 
  let () = Gen.Profiling.push_time_always "cache overhead" in
  let sf = norm_var_name f in
  let prover = string_of_prover !pure_tp  in
  let fstring = Cprinter.string_of_pure_formula sf in
  let fstring_with_prover = prover^fstring in
  let () = cache_sat_count := !cache_sat_count+1 in
  let () = cache_status := true in
  let () = Gen.Profiling.pop_time_always "cache overhead" in
  let res =
    try
      find_cache !sat_cache fstring fstring_with_prover
    with Not_found ->
      let () = cache_status := false in
      let r = is_sat f in
      let prover_str = if r then fstring_with_prover else fstring in
      (* cache only sound outcomes : unless we add prover name to it *)
      let () = Gen.Profiling.push_time_always "cache overhead" in
      let () = cache_sat_miss := !cache_sat_miss+1 in
      let () = Hashtbl.add !sat_cache prover_str r in
      let () = Gen.Profiling.pop_time_always "cache overhead" in
      r
  in res

let sat_cache is_sat (f:CP.formula) : bool = 
  let pr = Cprinter.string_of_pure_formula in
  let pr2 b = ("found?:"^(string_of_bool !cache_status)
               ^" ans:"^(string_of_bool b)) in
  Debug.no_1 "sat_cache" pr pr2 (sat_cache is_sat) f

let tp_is_sat (f:CP.formula) (old_sat_no :string) = 
  (* TODO WN : can below remove duplicate constraints? *)
  (* let f = CP.elim_idents f in *)
  (* this reduces x>=x to true; x>x to false *)
  let sat_num = next_proof_no () in
  let sat_no = (string_of_int sat_num) in
  x_dinfo_zp (lazy ("SAT #" ^ sat_no)) no_pos;
  x_dinfo_zp (lazy (!print_pure f)) no_pos;
  (* let tstart = Gen.Profiling.get_time () in		 *)
  let fn_sat f = (tp_is_sat_perm f) sat_no in
  let cmd = PT_SAT f in
  let () = Log.last_proof_command # set cmd in
  let logger fr tt timeout = 
    let tp = (string_of_prover !pure_tp) in
    let () = add_proof_logging timeout !cache_status old_sat_no sat_num tp  cmd tt
        (match fr with Some res -> PR_BOOL res | None -> PR_exception) in
    (Others.last_tp_used # string_of,sat_no)
  in
  let res = 
    (if !Globals.no_cache_formula then
       Timelog.log_wrapper "SAT-nocache" logger fn_sat f
     else
       (Timelog.log_wrapper "SAT" logger (sat_cache fn_sat)) f)
  in
  (* let tstop = Gen.Profiling.get_time () in *)
  res

let tp_is_sat f sat_no =
  Debug.no_1 "tp_is_sat" Cprinter.string_of_pure_formula string_of_bool 
    (fun f -> tp_is_sat f sat_no) f

let sel_related p_other p_bag =
  if p_other==[] then p_bag
  else
    let v_lst = List.concat (List.map (CP.fv) p_bag) in
    let nf = CP.find_rel_constraints_list p_other v_lst in
    nf::p_bag

let tp_conj_bag_sat f sat_no =
  let cl = CP.split_conjunctions f in
  let (sb,sp) = List.partition (CP.is_bag_constraint) cl in
  if sb==[] then tp_is_sat f sat_no
  else 
    let sb =  sel_related sp sb in
    let p1 (*bag*) = CP.join_conjunctions sb in
    let p2 (*pure*) = CP.join_conjunctions sp in
    (tp_is_sat p1 sat_no) && (tp_is_sat p2 sat_no) 

let tp_is_sat (f:CP.formula) (old_sat_no :string) =
  if !Globals.auto_eps_flag then
    (* this is mainly for mono prover *)
    let fl = CP.split_disjunctions_deep f in
    let f_or a b = a || b in
    List.fold_left (fun k f ->  k || (tp_conj_bag_sat f old_sat_no)) false fl
    (* List.fold_left (fun k f -> f_or k (tp_conj_bag_sat f old_sat_no)) false fl *)
  else tp_is_sat f old_sat_no

(* let tp_is_sat (f: CP.formula) (sat_no: string) do_cache = *)
(*   let pr = Cprinter.string_of_pure_formula in *)
(*   Debug.no_1 "tp_is_sat" pr string_of_bool (fun _ -> tp_is_sat f sat_no do_cache) f *)

(* in let add_inf_constr = BForm((mkLt (CP.Var(CP.SpecVar(Int,constinfinity,Primed),no_pos)) (CP.Var(CP.SpecVar(Int,constinfinity,Unprimed),no_pos)) no_pos,None),None) in *)

let norm_pure_input f =
  let f = x_add_1 cnv_ptr_to_int f in
  let f = if !Globals.allow_inf (*&& not(!Globals.allow_inf_qe_coq)*)
    then let f = Infinity.convert_inf_to_var f
      in let add_inf_constr = BForm((mkLt (CP.Var(CP.SpecVar(Int,constinfinity,Primed),no_pos)) (CP.Var(CP.SpecVar(Int,constinfinity,Unprimed),no_pos)) no_pos,None),None) in
      let f = mkAnd add_inf_constr f no_pos in f
    else f in f

let norm_pure_input f =
  let pr = Cprinter.string_of_pure_formula in
  let pr2 s = s # string_of in 
  (* let pr2 r = pr_pair Cprinter.string_of_pure_formula (fun s -> s#string_of) (r,imm_stk) in *)
  Debug.no_eff_2 "norm_pure_input2" [false;true] pr pr2 pr (fun _ _ -> norm_pure_input f) f imm_stk

let om_simplify f =
  (* wrap_pre_post x_add cnv_ptr_to_int norm_pure_result *)
  wrap_pre_post norm_pure_input (x_add_1 norm_pure_result)
    (x_add_1 Omega.simplify) f
(* let f = cnv_ptr_to_int f in *)
(* let r = Omega.simplify f in *)
(* cnv_int_to_ptr r *)

(* Take out formulas that omega cannot handle*)
(* let om_simplify f= *)
(*   Trans_arr.split_and_combine om_simplify (x_add_1 Trans_arr.can_be_simplify) f *)
(* ;; *)

let om_simplify f =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "simplify_omega" pr pr om_simplify f

let simplify_omega (f:CP.formula): CP.formula =
  if is_bag_constraint f then f
  else
    let neqs = CP.get_neqs_ptrs_form f in
    let simp_f = om_simplify f in
    CP.mkAnd simp_f neqs (CP.pos_of_formula f)

(* let simplify_omega (f:CP.formula): CP.formula =  *)
(*   if is_bag_constraint f then f *)
(*   else Omega.simplify f    *)

(* let simplify_omega f = *)
(*   Debug.no_1 "simplify_omega" *)
(* 	Cprinter.string_of_pure_formula *)
(* 	Cprinter.string_of_pure_formula *)
(* 	simplify_omega f *)

let simplify (f : CP.formula) : CP.formula =
  (* proof_no := !proof_no + 1; *)

  let simpl_num = next_proof_no () in
  let simpl_no = (string_of_int simpl_num) in
  if !Globals.no_simpl then f else
  if !perm=Dperm && CP.has_tscons f<>CP.No_cons then f
  else
    let cmd = PT_SIMPLIFY f in
    let () = Log.last_proof_command # set cmd in
    (* if !Globals.allow_inf_qe_coq then f else *)
    (* if !Globals.allow_inf && Infinity.contains_inf f then f
       else
       let f = if !Globals.allow_inf then Infinity.convert_inf_to_var f else f in*)
    let omega_simplify f = x_add_1 simplify_omega f
    (* Omega.simplify f  *)in
    (* this simplifcation will first remove complex formula as boolean
       vars but later restore them *)
    let z3_simplify f =
      if is_array_constraint f then f else
        let f = wrap_pre_post norm_pure_input norm_pure_result Smtsolver.simplify f in
        x_add CP.arith_simplify 13 f
    in
    let z3n_simplify f =
      if is_array_constraint f then f else
        let f = wrap_pre_post norm_pure_input norm_pure_result Z3.simplify f in
        x_add CP.arith_simplify 13 f
    in
    (*      let redlog_simplify f =  wrap_pre_post norm_pure_input norm_pure_result Redlog.simplify f in
            let mona_simplify f =  wrap_pre_post norm_pure_input norm_pure_result Mona.simplify f in *)
    if !external_prover then 
      match Netprover.call_prover (Simplify f) with
      | Some res -> res
      | None -> f
    else 
      begin
        let tstart = Gen.Profiling.get_time () in
        try
          if not !tp_batch_mode then start_prover ();
          Gen.Profiling.push_time "simplify";
          let fn f = 
            match !pure_tp with
            | DP -> Dp.simplify f
            | Isabelle -> Isabelle.simplify f
            | Coq -> 
              if (is_list_constraint f) then
                (Coq.simplify f)
              else ((*Omega*)Smtsolver.simplify f)
            | Mona | MonaH ->
              if (is_bag_constraint f) then
                (Mona.simplify f)
              else
                (* exist x, f0 ->  eexist x, x>0 /\ f0*)
                let f1 = CP.add_gte0_for_mona f in
                let f=(omega_simplify f1) in
                x_add CP.arith_simplify 12 f
            | OM ->
              if (is_bag_constraint f) then (Mona.simplify f)
              else
                let f=(omega_simplify f) in
                x_add CP.arith_simplify 12 f
            | OI ->
              if (is_bag_constraint f) then (Isabelle.simplify f)
              else (omega_simplify f)
            | SetMONA -> Mona.simplify f
            | CM ->
              if is_bag_constraint f then Mona.simplify f
              else omega_simplify f
            | Z3 -> z3_simplify f
            (* Smtsolver.simplify f *)
            | Z3N -> z3n_simplify f
            (* Smtsolver.simplify f *)
            | Redlog -> Redlog.simplify f
            | OCRed -> Redlog.simplify f
            | RM ->
              if is_bag_constraint f then Mona.simplify f
              else Redlog.simplify f
            | PARAHIP ->
              if is_bag_constraint f then
                Mona.simplify f
              else
                Redlog.simplify f
            | ZM -> 
              if is_bag_constraint f then Mona.simplify f
              else Smtsolver.simplify f
            | AUTO ->
              if (is_bag_constraint f) then (Mona.simplify f)
              else if (is_list_constraint f) then (Coq.simplify f)
              else if (is_array_constraint f) then (Smtsolver.simplify f)
              else (omega_simplify f)
            | OZ ->
              if (is_array_constraint f) then (Smtsolver.simplify f)
              else (omega_simplify f)
            | SPASS -> Spass.simplify f
            | LOG -> find_formula_proof_res simpl_no
            | _ -> omega_simplify f 
          in
          let fn f = 
            let r = fn f in
            let res = ( 
              (* if !Globals.do_slicing then *)
              if not !Globals.dis_slc_ann then
                let rel_vars_lst =
                  let bfl = CP.break_formula f in
                  (* let bfl_no_il = List.filter (fun (_,il) -> match il with *)
                  (* | None -> true | _ -> false) bfl in                      *)
                  (List.map (fun (svl,lkl,_) -> (svl,lkl)) (CP.group_related_vars bfl))
                in CP.set_il_formula_with_dept_list r rel_vars_lst
              else r
            )
            in res
          in
          let logger fr tt timeout = 
            let tp = (string_of_prover !pure_tp) in
            let () = add_proof_logging timeout !cache_status simpl_no simpl_num tp cmd tt 
                (match fr with Some res -> PR_FORMULA res | None -> PR_exception) in
            (tp,simpl_no)
          in
          let res = Timelog.log_wrapper "simplify" logger fn f in
          Gen.Profiling.pop_time "simplify";
          let tstop = Gen.Profiling.get_time () in
          if not !tp_batch_mode then stop_prover ();
          (*let () = print_string ("\nsimplify: f after"^(Cprinter.string_of_pure_formula r)) in*)
          (* To recreate <IL> relation after simplifying *)
          (* TODO : add logtime for simplify *)
          (* Why start/stop prver when interactive? *)
          res
        with | _ -> 
          let _= add_proof_logging false !cache_status simpl_no simpl_num (string_of_prover !pure_tp) cmd 
              (0.0) (PR_exception) in
          f
      end

let simplify f =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "(inner most) simplify" pr pr simplify f
;;

let om_pairwisecheck f =
  wrap_pre_post norm_pure_input norm_pure_result
    (* wrap_pre_post cnv_ptr_to_int norm_pure_result *)
    (x_add_1 Omega.pairwisecheck) f

(* ZH: Take out the array part *)
(* let om_pairwisecheck f = *)
(*   (\* let () = x_tinfo_pp "take out array part" no_pos in *\) *)
(*   Trans_arr.split_and_combine (x_add_1 om_pairwisecheck) (fun f-> not (Trans_arr.contain_array f)) f *)
(* ;; *)

let om_pairwisecheck f =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "om_pairwisecheck" pr pr om_pairwisecheck f

let tp_pairwisecheck2_x (f1 : CP.formula) (f2 : CP.formula) : CP.formula =
  if not !tp_batch_mode then Omega.start_prover ();
  let simpl_num = next_proof_no () in
  let simpl_no = (string_of_int simpl_num) in
  let f = CP.mkOr f1 f2 None no_pos in
  let cmd = PT_PAIRWISE f in
  let _ = Log.last_proof_command # set cmd in
  let fn f = Omega.pairwisecheck2 f1 f2 in
  let logger fr tt timeout =
    let tp = (string_of_prover !pure_tp) in
    let _ = add_proof_logging timeout !cache_status simpl_no simpl_num tp cmd tt
        (match fr with Some res -> PR_FORMULA res | None -> PR_exception) in
    (tp,simpl_no)
  in
  let res = Timelog.log_wrapper "pairwise2" logger fn f in
  if not !tp_batch_mode then Omega.stop ();
  res

let tp_pairwisecheck2 f1 (f2 : CP.formula) : CP.formula = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "tp_pairwisecheck2" pr pr pr tp_pairwisecheck2_x f1 f2


let tp_pairwisecheck (f : CP.formula) : CP.formula =
  if not !tp_batch_mode then start_prover ();
  let simpl_num = next_proof_no () in
  let simpl_no = (string_of_int simpl_num) in
  let cmd = PT_PAIRWISE f in
  let _ = Log.last_proof_command # set cmd in
  (*if !Globals.allow_inf && Infinity.contains_inf f then f
    else *)
  let fn f = match !pure_tp with
    | DP -> Dp.pairwisecheck f
    | Isabelle -> Isabelle.pairwisecheck f
    | Coq -> 
      if (is_list_constraint f) then (Coq.pairwisecheck f)
      else (Smtsolver.pairwisecheck f)
    | Mona 
    | OM ->
      if (is_bag_constraint f) then (Mona.pairwisecheck f)
      else (x_add_1 om_pairwisecheck f)
    | OI ->
      if (is_bag_constraint f) then (Isabelle.pairwisecheck f)
      else (x_add_1 om_pairwisecheck f)
    | SetMONA -> Mona.pairwisecheck f
    | CM ->
      if is_bag_constraint f then Mona.pairwisecheck f
      else x_add_1 om_pairwisecheck f
    | Z3 -> (* Smtsolver.pairwisecheck f *) x_add_1 om_pairwisecheck f
    | Z3N -> Z3.pairwisecheck f
    | Redlog -> Redlog.pairwisecheck f
    | OCRed -> Redlog.pairwisecheck f
    | Mathematica -> Mathematica.pairwisecheck f
    | RM ->
      if is_bag_constraint f then Mona.pairwisecheck f
      else Redlog.pairwisecheck f
    | ZM ->
      if is_bag_constraint f then Mona.pairwisecheck f
      else Smtsolver.pairwisecheck f
    | PARAHIP -> (*TOCHECK: what is it for? *)
      if is_bag_constraint f then Mona.pairwisecheck f
      else Redlog.pairwisecheck f
    | _ -> (x_add_1 om_pairwisecheck f) in
  let logger fr tt timeout = 
    let tp = (string_of_prover !pure_tp) in
    let _ = add_proof_logging timeout !cache_status simpl_no simpl_num tp cmd tt 
        (match fr with Some res -> PR_FORMULA res | None -> PR_exception) in
    (tp,simpl_no)
  in
  let res = Timelog.log_wrapper "pairwise" logger fn f in
  if not !tp_batch_mode then stop_prover ();
  res

let tp_pairwisecheck (f : CP.formula) : CP.formula = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "tp_pairwisecheck" pr pr tp_pairwisecheck f

let rec pairwisecheck_x (f : CP.formula) : CP.formula = 
  if no_andl f then  tp_pairwisecheck f 
  else
    let rec helper f =  match f with 
      | Or (p1, p2, lbl , pos) -> Or (pairwisecheck_x p1, pairwisecheck_x p2, lbl, pos)
      | AndList l -> AndList (map_l_snd tp_pairwisecheck l)
      | _ ->  tp_pairwisecheck f in
    helper f

let pairwisecheck (f : CP.formula) : CP.formula = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "pairwisecheck" pr pr pairwisecheck_x f



let pairwisecheck_raw (f : CP.formula) : CP.formula =
  let rels = CP.get_RelForm f in
  let ids = List.concat (List.map get_rel_id_list rels) in
  (* let pr = Cprinter.string_of_pure_formula in *)
  (* Debug.info_hprint (add_str "f" pr) f no_pos; *)
  let f_memo, subs, bvars = CP.memoise_rel_formula ids f in
  (* Debug.info_hprint (add_str "f_memo" pr) f_memo no_pos; *)
  (* Debug.info_hprint (add_str "bvars" !CP.print_svl) bvars no_pos; *)
  (* Debug.info_hprint (add_str "subs" (pr_list_ln (pr_pair !CP.print_sv pr))) subs no_pos; *)
  if CP.has_template_formula f_memo then f
  else
    let res_memo = pairwisecheck f_memo in
    (* Debug.info_hprint (add_str "res_memo" pr) res_memo no_pos; *)
    CP.restore_memo_formula subs bvars res_memo

let pairwisecheck_raw (f : CP.formula) : CP.formula =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "pairwisecheck_raw" pr pr pairwisecheck_raw f


(*for AndList it simplifies one batch at a time*)
let simplify (f:CP.formula):CP.formula =
  let rec helper f = match f with 
    (* | Or(f1,f2,lbl,pos) -> mkOr (helper f1) (helper f2) lbl pos *)
    (* | AndList b -> mkAndList (map_l_snd simplify b) *)
    (* | _ -> Trans_arr.translate_back_array_in_one_formula (tp_pairwisecheck (simplify f)) *)
    | _ ->
      (tp_pairwisecheck (simplify f)) in
  helper f
;;

let simplify f =
  Debug.no_1 "simplify##" !CP.print_formula !CP.print_formula simplify f
;;

let simplify_tp (f:CP.formula):CP.formula =
  let pr = !CP.print_formula in
  Debug.no_1 "TP.simplify" pr pr simplify f

let rec simplify_raw (f: CP.formula) =
  if not(!Globals.infer_raw_flag) then simplify_tp f
  else
    let is_bag_cnt = is_bag_constraint f in
    if is_bag_cnt then
      let () = y_tinfo_hp (add_str " xxxx bag: " (pr_id)) "bag" in
      let _,new_f = trans_dnf f in
      let disjs = list_of_disjs new_f in
      let disjs = List.map (fun disj -> 
          let rels = CP.get_RelForm disj in
          let disj = CP.drop_rel_formula disj in
          let (bag_cnts, others) = List.partition is_bag_constraint (list_of_conjs disj) in
          (* let () = Debug.info_hprint (add_str " xxxx others: " (pr_list_ln (!CP.print_formula))) others no_pos in *)
          let others = simplify_raw (conj_of_list others no_pos) in
          conj_of_list ([others]@bag_cnts@rels) no_pos
        ) disjs in
      List.fold_left (fun p1 p2 -> mkOr p1 p2 None no_pos) (mkFalse no_pos) disjs
    else
      (* let () = y_tinfo_pp "xxx rel " in *)
      let rels = CP.get_RelForm f in
      let ids = List.concat (List.map get_rel_id_list rels) in
      let f_memo, subs, bvars = CP.memoise_rel_formula ids f in
      if CP.has_template_formula f_memo then f
      else
        let res_memo = simplify_tp f_memo in
        let () = Debug.ninfo_hprint (add_str "bvars" (!CP.print_svl)) bvars no_pos in
        CP.restore_memo_formula subs bvars res_memo

let simplify_raw_w_rel (f: CP.formula) = 
  let is_bag_cnt = is_bag_constraint f in
  if is_bag_cnt then
    let _,new_f = trans_dnf f in
    let disjs = list_of_disjs new_f in
    let disjs = List.map (fun disj -> 
        let (bag_cnts, others) = List.partition is_bag_constraint (list_of_conjs disj) in
        let others = simplify (conj_of_list others no_pos) in
        conj_of_list (others::bag_cnts) no_pos
      ) disjs in
    List.fold_left (fun p1 p2 -> mkOr p1 p2 None no_pos) (mkFalse no_pos) disjs
  else simplify f

let simplify_raw f =
  let pr = !CP.print_formula in
  Debug.no_1 "simplify_raw" pr pr simplify_raw f

let simplify_exists_raw exist_vars (f: CP.formula) = 
  let is_bag_cnt = is_bag_constraint f in
  (* let () = *)
  (* if is_bag_cnt then print_endline ("is_bag_cnt:true") else print_endline ("is_bag_cnt:false") in *)
  if is_bag_cnt then
    let _,new_f = trans_dnf f in
    let disjs = list_of_disjs new_f in
    let disjs = List.map (fun disj -> 
        let (bag_cnts, others) = List.partition is_bag_constraint (list_of_conjs disj) in
        let others = simplify (CP.mkExists exist_vars (conj_of_list others no_pos) None no_pos) in
        let bag_cnts = List.filter (fun b -> CP.intersect (CP.fv b) exist_vars = []) bag_cnts in
        conj_of_list (others::bag_cnts) no_pos
      ) disjs in
    List.fold_left (fun p1 p2 -> mkOr p1 p2 None no_pos) (mkFalse no_pos) disjs
  else
    simplify (CP.mkExists exist_vars f None no_pos)
;;

let simplify_exists_raw exist_vars (f:CP.formula) =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "simplify_exists_raw" string_of_spec_var_list pr pr (fun e f-> simplify_exists_raw e f) exist_vars f
;;

(* always simplify directly with the help of prover *)
let simplify_always (f:CP.formula): CP.formula = 
  let () = Gen.Profiling.inc_counter ("stat_count_simpl") in
  simplify f 

let simplify (f:CP.formula): CP.formula = 
  x_add CP.elim_exists_with_simpl simplify f 

(* let simplify (f:CP.formula): CP.formula =  *)
(*   let pr = Cprinter.string_of_pure_formula in *)
(*   Debug.no_1 "TP.simplify" pr pr simplify f *)

let simplify (f : CP.formula) : CP.formula =
  let pf = Cprinter.string_of_pure_formula in
  Debug.no_1 "simplify(TP)" pf pf simplify f

let simplify_a (s:int) (f:CP.formula): CP.formula = 
  let pf = Cprinter.string_of_pure_formula in
  Debug.no_1_num s ("TP.simplify_a") pf pf simplify f

let oc_hull f =
  wrap_pre_post norm_pure_input norm_pure_result
    Omega.hull f

let hull (f : CP.formula) : CP.formula =
  let () = if no_andl f then () else report_warning no_pos "trying to do hull over labels!" in
  if not !tp_batch_mode then start_prover ();
  let simpl_num = next_proof_no () in
  let simpl_no = (string_of_int simpl_num) in
  let cmd = PT_HULL f in
  let () = Log.last_proof_command # set cmd in
  (*if !Globals.allow_inf && Infinity.contains_inf f then f
    else*) 
  (*let f = if !Globals.allow_inf then Infinity.convert_inf_to_var f else f in*)
  let fn f = match !pure_tp with
    | DP -> Dp.hull  f
    | Isabelle -> Isabelle.hull f
    | Coq -> (* Coq.hull f *)
      if (is_list_constraint f) then (Coq.hull f)
      else ((*Omega*)Smtsolver.hull f)
    | Mona   -> Mona.hull f  
    | MonaH
    | OM ->
      if (is_bag_constraint f) then (Mona.hull f)
      else (oc_hull f)
    | OI ->
      if (is_bag_constraint f) then (Isabelle.hull f)
      else (oc_hull f)
    | SetMONA -> Mona.hull f
    | CM ->
      if is_bag_constraint f then Mona.hull f
      else oc_hull f
    | Z3 -> Smtsolver.hull f
    | Z3N -> Z3.hull f
    | Redlog -> Redlog.hull f
    | OCRed -> Redlog.hull f
    | Mathematica -> Mathematica.hull f
    | RM ->
      if is_bag_constraint f then Mona.hull f
      else Redlog.hull f
    | ZM ->
      if is_bag_constraint f then Mona.hull f
      else Smtsolver.hull f
    | _ -> (oc_hull f) in
  let logger fr tt timeout = 
    let tp = (string_of_prover !pure_tp) in
    let () = add_proof_logging timeout !cache_status simpl_no simpl_num tp cmd tt 
        (match fr with Some res -> PR_FORMULA res | None -> PR_exception) in
    (tp,simpl_no)
  in
  let res = Timelog.log_wrapper "hull" logger fn f in
  if not !tp_batch_mode then stop_prover ();
  res

(* this extracts basic conjunct prior to hulling the disj form remainder *)
let clever_hull f =
  let x = CP.split_conjunctions f in
  let (others,basic) = List.partition (CP.is_disjunct) x in
  if others==[] then f
  else
    (* let x = []@[] in *)
    (* let z = [] in *)
    (* let z = [] in *)
    let others = hull(CP.join_conjunctions others) in
    CP.join_conjunctions (others::basic)

(* let k f = [] *)

let hull (f : CP.formula) : CP.formula =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "hull" pr pr clever_hull f


let om_pairwisecheck f =
  wrap_pre_post norm_pure_input norm_pure_result
    (* wrap_pre_post cnv_ptr_to_int norm_pure_result *)
    (x_add_1 Omega.pairwisecheck) f 

let om_pairwisecheck f =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "om_pairwisecheck(2)" pr pr om_pairwisecheck f

let tp_pairwisecheck2_x (f1 : CP.formula) (f2 : CP.formula) : CP.formula =
  if not !tp_batch_mode then Omega.start_prover ();
  let simpl_num = next_proof_no () in
  let simpl_no = (string_of_int simpl_num) in
  let f = CP.mkOr f1 f2 None no_pos in
  let cmd = PT_PAIRWISE f in
  let () = Log.last_proof_command # set cmd in
  let fn f = Omega.pairwisecheck2 f1 f2 in
  let logger fr tt timeout =
    let tp = (string_of_prover !pure_tp) in
    let () = add_proof_logging timeout !cache_status simpl_no simpl_num tp cmd tt
        (match fr with Some res -> PR_FORMULA res | None -> PR_exception) in
    (tp,simpl_no)
  in
  let res = Timelog.log_wrapper "pairwise2" logger fn f in
  if not !tp_batch_mode then Omega.stop ();
  res

let tp_pairwisecheck2 f1 (f2 : CP.formula) : CP.formula = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "tp_pairwisecheck2" pr pr pr tp_pairwisecheck2_x f1 f2


let tp_pairwisecheck (f : CP.formula) : CP.formula =
  if not !tp_batch_mode then start_prover ();
  let simpl_num = next_proof_no () in
  let simpl_no = (string_of_int simpl_num) in
  let cmd = PT_PAIRWISE f in
  let () = Log.last_proof_command # set cmd in
  (*if !Globals.allow_inf && Infinity.contains_inf f then f
    else *)
  let fn f = match !pure_tp with
    | DP -> Dp.pairwisecheck f
    | Isabelle -> Isabelle.pairwisecheck f
    | Coq -> 
      if (is_list_constraint f) then (Coq.pairwisecheck f)
      else (Smtsolver.pairwisecheck f)
    | Mona 
    | OM ->
      if (is_bag_constraint f) then (Mona.pairwisecheck f)
      else (x_add_1 om_pairwisecheck f)
    | OI ->
      if (is_bag_constraint f) then (Isabelle.pairwisecheck f)
      else (x_add_1 om_pairwisecheck f)
    | SetMONA -> Mona.pairwisecheck f
    | CM ->
      if is_bag_constraint f then Mona.pairwisecheck f
      else x_add_1 om_pairwisecheck f
    | Z3 -> (* Smtsolver.pairwisecheck f *) om_pairwisecheck f
    | Z3N -> Z3.pairwisecheck f
    | Redlog -> Redlog.pairwisecheck f
    | OCRed -> Redlog.pairwisecheck f
    | Mathematica -> Mathematica.pairwisecheck f
    | RM ->
      if is_bag_constraint f then Mona.pairwisecheck f
      else Redlog.pairwisecheck f
    | ZM ->
      if is_bag_constraint f then Mona.pairwisecheck f
      else Smtsolver.pairwisecheck f
    | PARAHIP -> (*TOCHECK: what is it for? *)
      if is_bag_constraint f then Mona.pairwisecheck f
      else Redlog.pairwisecheck f
    | _ -> (x_add_1 om_pairwisecheck f) in
  (* let fn f = wrap_pre_post norm_pure_input norm_pure_result fn f in *)
  let logger fr tt timeout = 
    let tp = (string_of_prover !pure_tp) in
    let () = add_proof_logging timeout !cache_status simpl_no simpl_num tp cmd tt 
        (match fr with Some res -> PR_FORMULA res | None -> PR_exception) in
    (tp,simpl_no)
  in
  let res = Timelog.log_wrapper "pairwise" logger fn f in
  if not !tp_batch_mode then stop_prover ();
  res

let rec pairwisecheck_x (f : CP.formula) : CP.formula = 
  if no_andl f then  tp_pairwisecheck f 
  else
    let rec helper f =  match f with 
      | Or (p1, p2, lbl , pos) -> Or (pairwisecheck_x p1, pairwisecheck_x p2, lbl, pos)
      | AndList l -> AndList (map_l_snd tp_pairwisecheck l)
      | _ ->  tp_pairwisecheck f in
    helper f

let pairwisecheck (f : CP.formula) : CP.formula = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "pairwisecheck" pr pr pairwisecheck_x f



let pairwisecheck_raw (f : CP.formula) : CP.formula =
  let rels = CP.get_RelForm f in
  let ids = List.concat (List.map get_rel_id_list rels) in
  (* let pr = Cprinter.string_of_pure_formula in *)
  (* Debug.info_hprint (add_str "f" pr) f no_pos; *)
  let f_memo, subs, bvars = CP.memoise_rel_formula ids f in
  (* Debug.info_hprint (add_str "f_memo" pr) f_memo no_pos; *)
  (* Debug.info_hprint (add_str "bvars" !CP.print_svl) bvars no_pos; *)
  (* Debug.info_hprint (add_str "subs" (pr_list_ln (pr_pair !CP.print_sv pr))) subs no_pos; *)
  if CP.has_template_formula f_memo then f
  else
    let res_memo = pairwisecheck f_memo in
    (* Debug.info_hprint (add_str "res_memo" pr) res_memo no_pos; *)
    CP.restore_memo_formula subs bvars res_memo

let pairwisecheck_raw (f : CP.formula) : CP.formula =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "pairwisecheck_raw" pr pr pairwisecheck_raw f


let simplify_with_pairwise (f : CP.formula) : CP.formula =
  let pf = Cprinter.string_of_pure_formula in
  x_ninfo_hp (add_str "simplifyX(input)" pf) f no_pos;
  let f1 = simplify_raw f in
  x_ninfo_hp (add_str "simplifyX(output)" pf) f1 no_pos;
  let f2 = pairwisecheck_raw f1 in
  x_ninfo_hp (add_str "simplifyX(pairwise)" pf) f2 no_pos;
  f2

let simplify_with_pairwise (s:int) (f:CP.formula): CP.formula =
  let pf = Cprinter.string_of_pure_formula in
  Debug.no_1_num s ("TP.simplify_with_pairwise") pf pf simplify_with_pairwise f

let should_output () = !print_proof && not !suppress_imply_out

let suppress_imply_output () = suppress_imply_out := true

let unsuppress_imply_output () = suppress_imply_out := false

let suppress_imply_output_stack = ref ([] : bool list)

let push_suppress_imply_output_state () = 
  suppress_imply_output_stack := !suppress_imply_out :: !suppress_imply_output_stack

let restore_suppress_imply_output_state () = match !suppress_imply_output_stack with
  | [] -> suppress_imply_output ()
  | h :: t -> begin
      suppress_imply_out := h;
      suppress_imply_output_stack := t;
    end

let tp_imply_translate_cyclic_x ante conseq =
  (*
    CASE 1:

    ante & acyclic(B) |- false      concrete(B,ante)
    -----------------------------------------------
    ante |- cyclic(B)
  *)
  let ante = concretize_bag_pure ante in
  let _ , c_rels = CP.extract_cyclic_rel_pure conseq in
  if (check_concrete_cyclic_rel_pure ante c_rels) then
    (* CASE 1 *)
    let to_ante = CP.from_cyclic_to_acyclic_rel_pure conseq in
    let new_ante = CP.mkAnd ante to_ante no_pos in
    let new_ante = CP. translate_acyclic_pure new_ante in
    let new_conseq = CP.mkFalse no_pos in
    (new_ante,new_conseq)
  else
    (ante,conseq)

(* For cyclic() relation *)
let tp_imply_translate_cyclic ante conseq =
  let pr = Cprinter.string_of_pure_formula in
  let pr_out = pr_pair pr pr in
  Debug.no_2 "tp_imply_translate_cyclic" pr pr pr_out
    tp_imply_translate_cyclic_x ante conseq

let tp_imply_translate_waitS_x ante conseq =
  let ante = concretize_bag_pure ante in
  let new_ante = CP.translate_waitS_pure ante in
  let concrete_bags = get_concrete_bag_pure ante in
  let concrete_bags = List.map (fun (v,exps) ->
      let vars = find_closure_pure_formula v ante in
      List.map (fun v -> (v,exps)) vars ) concrete_bags in
  let concrete_bags = List.concat concrete_bags in
  (* Use concrete bag in ante to instantiate conseq*)
  let nf , rels = CP.extract_waitS_rel_pure conseq in
  let fs = List.map (create_waitS_rel concrete_bags nf) rels in
  let new_conseq = List.fold_left (fun res f1 -> mkAnd res f1 no_pos) nf fs in
  (new_ante, new_conseq)

(* For waitS() relation *)
let tp_imply_translate_waitS ante conseq =
  let pr = Cprinter.string_of_pure_formula in
  let pr_out = pr_pair pr pr in
  Debug.no_2 "tp_imply_translate_waitS" pr pr pr_out
    tp_imply_translate_waitS_x ante conseq

(* check for concrete(S) *)
let tp_imply_concrete_rel_x ante conseq : bool =
  let ante = CP.concretize_bag_pure ante in
  let concrete_bags = get_concrete_bag_pure ante in
  let concrete_bags = List.map (fun (v,exps) ->
      let vars = find_closure_pure_formula v ante in
      List.map (fun v -> (v,exps)) vars ) concrete_bags
  in
  let concrete_bags = List.concat concrete_bags in
  let nf, rels = CP.extract_concrete_rel_pure conseq in
  let helper rel =
    (match rel with
     | RelForm (_,exps,_) ->
       let vs = afv (List.hd exps) in (* vs = [S]*)
       List.for_all (fun v1 -> List.exists (fun (v2,_) -> CP.eq_spec_var v1 v2) concrete_bags) vs
     | _ -> report_error no_pos ("tp_imply_concrete_rel: expect RelForm only"))
  in
  let res = and_list (List.map helper rels) in
  res

(* check for concrete(S) *)
let tp_imply_concrete_rel ante conseq : bool =
  let pr = Cprinter.string_of_pure_formula in
  let pr_out = string_of_bool in
  Debug.no_2 "tp_imply_concrete_rel" pr pr pr_out
    tp_imply_concrete_rel_x ante conseq

(*
  Preprocess/translate ante and conseq before doing
  actual tp_imply

  Return:
  None -> continue normally with the return ante, conseq. (default is (true,ante,conseq))
  Some res -> stop with res
*)
let tp_imply_preprocess_x (ante: CP.formula) (conseq: CP.formula) : (bool option * CP.formula * CP.formula) =
  if (CP.is_concrete_rel conseq) then
    let res = tp_imply_concrete_rel ante conseq in
    (Some res, ante, conseq)
  else
    let ante = if (has_waitS_rel_pure ante) then CP.translate_waitS_pure ante else ante in
    let ante,conseq = if (is_waitS_rel conseq) then tp_imply_translate_waitS ante conseq else (ante,conseq) in
    let ante,conseq = if (is_cyclic_rel conseq) then tp_imply_translate_cyclic ante conseq else (ante,conseq) in
    let ante = if (has_acyclic_rel_pure ante) then CP.translate_acyclic_pure ante else ante in
    let ante, conseq = x_add CP.translate_tup2_imply ante conseq in
    let ante,conseq =
      if (!Globals.allow_locklevel) then
        (*should translate waitlevel before level*)
        let ante = CP.infer_level_pure ante in (*add l.mu>0*)
        let ante = CP.translate_waitlevel_pure ante in
        let ante = CP.translate_level_pure ante in
        let conseq = CP.infer_level_pure conseq in (*add l.mu>0*)
        let conseq = CP.translate_waitlevel_pure conseq in
        let conseq = CP.translate_level_pure conseq in
        let () = x_dinfo_hp (add_str "After translate_: ante = " Cprinter.string_of_pure_formula) ante no_pos in
        let () = x_dinfo_hp (add_str "After translate_: conseq = " Cprinter.string_of_pure_formula) conseq no_pos in
        (ante,conseq)
      else 
        (* let ante = CP.drop_svl_pure ante [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in *)
        (* let ante = CP.drop_locklevel_pure ante in *)
        (* let conseq = CP.drop_svl_pure conseq [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in *)
        (* let conseq = CP.drop_locklevel_pure conseq in *)
        (ante,conseq)
    in (None, ante, conseq)


let tp_imply_preprocess (ante: CP.formula) (conseq: CP.formula) : (bool option * CP.formula * CP.formula) = 
  let pr = Cprinter.string_of_pure_formula in
  let pr_out = pr_triple (pr_option string_of_bool) pr pr in
  Debug.no_2 "tp_imply_preprocess" (add_str "ante" pr) (add_str "conseq" pr) pr_out
    tp_imply_preprocess_x ante conseq


let tp_imply_no_cache ante conseq imp_no timeout process =
  (* let _ = print_endline ("##Before process: ante: "^(Cprinter.string_of_pure_formula ante)^"\n conseq: "^(Cprinter.string_of_pure_formula conseq)) in *)
  (* let _ = print_endline ("##After process: ante: "^(Cprinter.string_of_pure_formula n_ante)^"\n conseq: "^(Cprinter.string_of_pure_formula n_conseq)) in *)
  (* let _ = print_endline ("tp_imply_no_cache n_ante: "^(Cprinter.string_of_pure_formula n_ante)) in *)
  (* let _ = print_endline ("tp_imply_no_cache n_conseq: "^(Cprinter.string_of_pure_formula n_conseq)) in *)
  (*let _ = print_endline ("Before Drop ante: "^(Cprinter.string_of_pure_formula n_ante)^" conseq: "^(Cprinter.string_of_pure_formula n_conseq)) in*)
  (* let n_ante = drop_array_formula n_ante in *)
  (* let n_conseq = drop_array_formula n_conseq in *)
  (*let _ = print_endline ("After Drop ante: "^(Cprinter.string_of_pure_formula d_ante)^" conseq: "^(Cprinter.string_of_pure_formula d_conseq)) in*)
  (* let _ = print_endline ("tp_imply_no_cache ante (after drop): "^(Cprinter.string_of_pure_formula ante)) in *)
  (* let _ = print_endline ("tp_imply_no_cache conseq (after drop): "^(Cprinter.string_of_pure_formula conseq)) in *)
  (*let _ = CP.filter_bag_constrain ante conseq in*)
  (**************************************)
  let res,ante,conseq = x_add tp_imply_preprocess ante conseq in
  match res with | Some ret -> ret | None -> (*continue normally*)
    (**************************************)
    (* ============================================================== *)
    (* superceded by add_imm_inv which is only done for ante of imply *)
    (* ============================================================== *)
    (* let vrs = Cpure.fv ante in *)
    (* let vrs = (Cpure.fv conseq)@vrs in *)
    (* let imm_vrs = List.filter (fun x -> (CP.type_of_spec_var x) == AnnT) vrs in  *)
    (* let imm_vrs = CP.remove_dups_svl imm_vrs in *)
    (* (\* add invariant constraint @M<:v<:@A for each annotation var *\) *)
    (* let ante = CP.add_ann_constraints imm_vrs ante in *)
    (* Handle Infinity Constraints *)
    let ante,conseq  = if !Globals.allow_inf (*&& !Globals.allow_inf_qe_coq
                                               then let a,c = (Infinity.convert_inf_to_var ( x_add Cpure.arith_simplify 333 ante)),
                                               (Infinity.convert_inf_to_var ( x_add Cpure.arith_simplify 332 conseq)) in a,c
                                               else if !Globals.allow_inf*)
      then let a,c = Infinity.normalize_inf_formula_imply ante conseq
        in let a = Infinity.fixed_point_pai_num a in a,c
      else ante,conseq in
    if should_output () then (
      reset_generated_prover_input ();
      reset_prover_original_output ();
    );
    let (pr_weak,pr_strong) = CP.drop_complex_ops in
    let (pr_weak_z3,pr_strong_z3) = CP.drop_complex_ops_z3 in
    let ante_w = ante in
    let conseq_s = conseq in
    let omega_imply a c = Omega.imply_ops pr_weak pr_strong a c imp_no timeout in
    let redlog_imply a c = wrap_redlog (Redlog.imply_ops pr_weak pr_strong a c) imp_no (* timeout *) in
    let oc_redlog_imply a c = wrap_ocredlog (Redlog.imply_ops pr_weak pr_strong a c) imp_no (* timeout *) in
    let mathematica_imply a c = Mathematica.imply_ops pr_weak pr_strong a c imp_no (* timeout *) in
    let mona_imply a c = Mona.imply_ops pr_weak pr_strong a c imp_no in
    let coq_imply a c = Coq.imply_ops pr_weak pr_strong a c in
    let z3_imply a c = Smtsolver.imply_ops pr_weak_z3 pr_strong_z3 a c timeout in
    let z3n_imply a c = Z3.imply_ops_cex pr_weak_z3 pr_strong_z3 a c timeout in
    if not !tp_batch_mode then start_prover ();
    let r = (
      match !pure_tp with
      | DP ->
        let r = Dp.imply ante_w conseq_s (imp_no^"XX") timeout in
        if test_db then
          let r2 = z3_imply (* Smtsolver.imply *) ante conseq (*(imp_no^"XX")*) (* timeout *) in
          if r=r2 then r
          else 
            failwith ("dp-omega imply mismatch on: "^(Cprinter.string_of_pure_formula ante)^"|-"^(Cprinter.string_of_pure_formula conseq)^
                      " d:"^(string_of_bool r)^" o:"^(string_of_bool r2)^"\n")
        else r
      | OmegaCalc ->
        if (CP.is_float_formula ante) || (CP.is_float_formula conseq) then
          redlog_imply ante_w conseq_s
        else (omega_imply ante conseq)
      | CvcLite -> Cvclite.imply ante_w conseq_s
      | Cvc4 -> (
          match process with
          | Some (Some proc, _) -> Cvc4.imply_increm process ante conseq imp_no
          | _ -> Cvc4.imply_increm (Some (!provers_process,true)) ante conseq imp_no
        )
      | Z3 -> 
        (* let _ = print_endline ("z3 ante"^(Cprinter.string_of_pure_formula ante)) in *)
        (* let _ = print_endline ("z3 conseq"^(Cprinter.string_of_pure_formula conseq)) in *)
        z3_imply ante conseq
      | Z3N -> z3n_imply ante conseq
      | Isabelle -> Isabelle.imply ante_w conseq_s imp_no
      | Coq ->
        if (is_list_constraint ante) || (is_list_constraint conseq) then
          ( coq_imply ante_w conseq_s)
        else ( z3_imply ante conseq)
      | AUTO ->
        if (is_bag_constraint ante) || (is_bag_constraint conseq) then
          (mona_imply ante_w conseq_s)
        else if (is_list_constraint ante) || (is_list_constraint conseq) then
          (coq_imply ante_w conseq_s)
        else if (is_array_constraint ante) || (is_array_constraint conseq) then
          ( z3_imply ante conseq)
        else
          (omega_imply ante conseq);
      | OZ ->
        if (is_array_constraint ante) || (is_array_constraint conseq) then
          ((* called_prover :="smtsolver "; *) z3_imply ante conseq)
        else
          ((* called_prover :="omega "; *) omega_imply ante conseq)
      | Mona | MonaH -> mona_imply ante_w conseq_s 
      | CO -> (
          let result1 = Cvc4.imply_helper_separate_process ante conseq imp_no in
          match result1 with
          | Some f -> f
          | None -> (* CVC Lite is not sure is this case, try Omega *)
            omega_count := !omega_count + 1;
            omega_imply ante conseq 
        )
      | CM -> (
          if (is_bag_constraint ante) || (is_bag_constraint conseq) then
            mona_imply ante_w conseq_s
          else
            let result1 = Cvc4.imply_helper_separate_process ante conseq imp_no in
            match result1 with
            | Some f -> f
            | None -> (* CVC Lite is not sure is this case, try Omega *)
              omega_count := !omega_count + 1;
              omega_imply ante conseq
        )
      | OM ->
        if (is_bag_constraint ante) || (is_bag_constraint conseq) then
          ((* called_prover :="mona " ; *) mona_imply ante_w conseq_s)
        else ((* called_prover :="omega " ; *) omega_imply ante conseq)
      | OI ->
        if (is_bag_constraint ante) || (is_bag_constraint conseq) then
          (Isabelle.imply ante_w conseq_s imp_no)
        else (omega_imply ante conseq)
      | SetMONA -> Setmona.imply ante_w conseq_s 
      | Redlog -> redlog_imply ante_w conseq_s  
      | OCRed -> oc_redlog_imply ante_w conseq_s  
      | Mathematica -> mathematica_imply ante_w conseq_s  
      | RM ->
        (*use UNSOUND approximation
          a & b -> c&d ~~~ (a->c) & (b->d)*)
        (*TO CHECK*)
        if (is_bag_constraint ante) && (is_float_formula ante) then
          let ante_no_float = CP.drop_float_formula ante in
          let ante_no_bag = CP.drop_bag_formula ante in
          let conseq_no_float = CP.drop_float_formula conseq in
          let conseq_no_bag = CP.drop_bag_formula conseq in
          let b_no_float = mona_imply ante_no_float conseq_no_float in
          let b_no_bag = mona_imply ante_no_bag conseq_no_bag in
          (b_no_float && b_no_bag)
        else
        if (is_bag_constraint ante) || (is_bag_constraint conseq) then
          mona_imply ante_w conseq_s
        else
          redlog_imply ante_w conseq_s
      | PARAHIP ->
        (*use UNSOUND approximation
          a & b -> c&d ~~~ (a->c) & (b->d)*)
        (*TO CHECK*)
        let is_rel_ante = is_relation_constraint ante in
        let is_rel_conseq = is_relation_constraint conseq in
        let is_bag_ante = is_bag_constraint_weak ante in
        let is_bag_conseq = is_bag_constraint_weak conseq in
        let is_float_ante = is_float_formula ante in
        let is_float_conseq = is_float_formula conseq in
        if (is_rel_ante || is_rel_conseq) && (is_bag_ante || is_bag_conseq) && (is_float_ante || is_float_conseq) then
          let ante_no_float_rel = CP.drop_rel_formula (CP.drop_float_formula ante) in
          let ante_no_bag_rel = CP.drop_rel_formula (CP.drop_bag_formula ante) in
          let ante_no_bag_float = CP.drop_float_formula (CP.drop_bag_formula ante) in
          let conseq_no_float_rel = CP.drop_rel_formula (CP.drop_float_formula conseq) in
          let conseq_no_bag_rel = CP.drop_rel_formula (CP.drop_bag_formula conseq) in
          let conseq_no_bag_float = CP.drop_float_formula (CP.drop_bag_formula conseq) in
          let b_no_float_rel = mona_imply ante_no_float_rel conseq_no_float_rel in
          let b_no_bag_rel = redlog_imply ante_no_bag_rel conseq_no_bag_rel in
          let b_no_bag_float = z3_imply ante_no_bag_float conseq_no_bag_float in
          (b_no_float_rel && b_no_bag_rel && b_no_bag_float)
        else
        if (is_bag_ante || is_bag_conseq) && (is_float_ante || is_float_conseq) then
          let ante_no_float = CP.drop_float_formula ante in
          let ante_no_bag = CP.drop_bag_formula ante in
          let conseq_no_float = CP.drop_float_formula conseq in
          let conseq_no_bag = CP.drop_bag_formula conseq in
          (* let () = print_endline (" ### ante_no_float = " ^ (Cprinter.string_of_pure_formula ante_no_float)) in *)
          (* let () = print_endline (" ### conseq_no_float = " ^ (Cprinter.string_of_pure_formula conseq_no_float)) in *)
          (* let () = print_endline (" ### ante_no_bag = " ^ (Cprinter.string_of_pure_formula ante_no_bag)) in *)
          (* let () = print_endline (" ### conseq_no_bag = " ^ (Cprinter.string_of_pure_formula conseq_no_bag)) in *)
          let b_no_float = mona_imply ante_no_float conseq_no_float in
          let b_no_bag = redlog_imply ante_no_bag conseq_no_bag in
          (b_no_float && b_no_bag)
        else
        if (is_bag_ante || is_bag_conseq) && (is_rel_ante || is_rel_conseq) then
          let ante_no_rel = CP.drop_rel_formula ante in
          let ante_no_bag = CP.drop_bag_formula ante in
          let conseq_no_rel = CP.drop_rel_formula conseq in
          let conseq_no_bag = CP.drop_bag_formula conseq in
          let b_no_rel = mona_imply ante_no_rel conseq_no_rel in
          let b_no_bag = z3_imply ante_no_bag conseq_no_bag in
          (b_no_rel && b_no_bag)
        else
        if (is_rel_ante) || (is_rel_conseq) then
          (* let ante = CP.drop_bag_formula (CP.drop_float_formula ante) in *)
          (* let conseq = CP.drop_bag_formula (CP.drop_float_formula conseq) in *)
          z3_imply ante conseq
        else if (is_bag_ante) || (is_bag_conseq) then
          if not (is_bag_conseq) then
            let ante_no_bag = CP.drop_bag_formula_weak ante_w in
            let ante_bag = CP.collect_all_constraints is_bag_constraint ante_w in
            let res1 = z3_imply ante_no_bag conseq_s in
            if (res1) then res1 else
              (* z3 may fail due to insufficient information -> try mona *)
              mona_imply ante_bag conseq_s
          else
            mona_imply ante_w conseq_s
        else if (is_float_ante || is_float_conseq) then
          redlog_imply ante_w conseq_s
        else
          z3_imply ante_w conseq_s
      | ZM -> 
        if (is_bag_constraint ante) || (is_bag_constraint conseq) then
          ((* called_prover := "mona "; *) mona_imply ante_w conseq_s)
        else z3_imply ante conseq
      | SPASS -> Spass.imply ante conseq timeout
      | MINISAT -> Minisat.imply ante conseq timeout
      | LOG -> find_bool_proof_res imp_no 
    ) in

    if not !tp_batch_mode then stop_prover ();
    (* let tstop = Gen.Profiling.get_time () in *)
    Gen.Profiling.push_time "tp_is_sat"; 
    if should_output () then (
      Prooftracer.push_pure_imply ante conseq r;
      Prooftracer.push_pop_prover_input (get_generated_prover_input ()) (string_of_prover !pure_tp);
      Prooftracer.push_pop_prover_output (get_prover_original_output ()) (string_of_prover !pure_tp);
      Prooftracer.add_pure_imply ante conseq r (string_of_prover !pure_tp) (get_generated_prover_input ()) (get_prover_original_output ());
      Prooftracer.pop_div ();
    );
    let () = Gen.Profiling.pop_time "tp_is_sat" in 
    r


let tp_imply_no_cache ante conseq imp_no timeout process =
  let ante,conseq = if !Globals.simpl_unfold3 then simpl_equalities ante conseq else (ante,conseq) in
  (* let ante =  *)
  (*   if !Globals.allow_imm_inv then add_imm_inv ante conseq *)
  (*   else ante in *)
  let ante = x_add_1 cnv_ptr_to_int ante in
  let conseq = cnv_ptr_to_int_weak conseq in
  let flag = tp_imply_no_cache ante conseq imp_no timeout process in
  if !Globals.allow_inf && !Globals.allow_inf_qe
  then
    (* the following is not complete as it does not expand the conseq quantifiers over PAInf *)
    (* let exists_inf f =  *)
    (*   let alist  = Infinity.quantifier_elim f in *)
    (*   let rec aux al = match al with *)
    (*     | [] -> false *)
    (*     | x::xs -> let f = tp_imply_no_cache x conseq imp_no timeout process in *)
    (*                (\*let _ = print_endline ("Ante :"^(Cprinter.string_of_pure_formula x)) in*\) *)
    (*                if f then true else aux xs *)
    (*   in aux alist in *)
    (*   let forall_lst = Infinity.get_inst_forall ante in  *)
    (*   let forall_lst = ante::forall_lst in *)
    (*   let f = List.for_all (fun c -> exists_inf c) forall_lst in f *)
    (*   let expand_quantifier f  =  *)
    (*   let forall_lst = Infinity.get_inst_forall f in *)
    (*   let forall_lst = ante::forall_lst in *)
    (*   conj_of_list  *)
    (*    (List.map (fun c -> disj_of_list (Infinity.quantifier_elim c) no_pos) forall_lst) no_pos in *)
    let expand_quantifier = Infinity.elim_forall_exists in
    tp_imply_no_cache (expand_quantifier ante) (expand_quantifier conseq) imp_no timeout process
  else if !Globals.allow_inf && !Globals.allow_inf_qe_coq then
    (*let f = mkAnd ante (mkNot_dumb conseq None no_pos) no_pos in
      let f = mkForall (fv f) f None no_pos in*)
    (*let func a c = 
      let f = Coqinf.check_imply_inf_formula ante conseq in
      Omega.is_valid f timeout in
      let fl = CP.split_disjunctions_deep ante in
      let rec aux al = match al with
      | [] -> false
      | x::xs -> if (func x conseq) then true else aux xs
      in aux fl*)
    let f  = Coqinf.check_imply_inf_formula ante conseq in
    Omega.is_valid f timeout
    (* not(Omega.is_sat f imp_no)*)
    (*(tp_is_sat_no_cache f imp_no)*)
    (* tp_imply_no_cache (Coqinf.check_sat_inf_formula  ante) 
       (Coqinf.check_sat_inf_formula conseq) imp_no timeout process*)
  else flag 

let add_imm_inv_wrap f ante conseq = 
  let ante = 
    if !Globals.allow_imm_inv then add_imm_inv ante conseq
    else ante in
  (* enable aggressive im simplification only when imm guards are added *)
  Wrapper.wrap_one_bool Globals.aggressive_imm_simpl !Globals.allow_imm_inv f ante

let tp_imply_no_cache ante conseq imp_no timeout process =
  add_imm_inv_wrap (fun ante -> tp_imply_no_cache ante conseq imp_no timeout process) ante conseq
  

(* let tp_imply_no_cache ante conseq imp_no timeout process = *)
(* 	(\*wrapper for capturing equalities due to transitive equality with null*\) *)
(* 	let enull = CP.Var (CP.SpecVar(Void,"NULLV",Unprimed),no_pos) in *)
(* 	let f_e _ (e,r) = match e with  *)
(* 		| CP.Eq(CP.Null _,CP.Var v,p2) -> Some ( (CP.Eq(enull, CP.Var v,p2),r), true) *)
(* 		| CP.Eq(CP.Var v,CP.Null _,p2) -> Some ( (CP.Eq(CP.Var v, enull,p2),r), true) *)
(* 		| _ -> None in *)
(* 	let transformer_fct = (fun _ _ -> None),f_e,(fun _ _ -> None) in *)
(* 	let tr_arg = (fun _ _->()),(fun _ _->()),(fun _ _->()) in *)
(* 	let ante,did = trans_formula ante ()  transformer_fct tr_arg (fun x -> List.exists (fun x->x) x) in *)
(* 	let ante = if did then  And(ante, (CP.mkNull (CP.SpecVar(Void,"NULLV",Unprimed)) no_pos) ,no_pos)  *)
(* 			   else ante in *)
(* 	tp_imply_no_cache ante conseq imp_no timeout process *)

let tp_imply_no_cache ante conseq imp_no timeout process =
  let pr = Cprinter.string_of_pure_formula in
  let _ = CP.filter_bag_constrain ante conseq in
  Debug.no_4(* _loop *) "tp_imply_no_cache" pr pr (fun s -> s) string_of_prover string_of_bool
    (fun _ _ _ _ -> tp_imply_no_cache ante conseq imp_no timeout process) ante conseq imp_no !pure_tp

let tp_imply_perm ante conseq imp_no timeout process = 
  if !perm=Dperm then
    let conseq = Perm.drop_tauto conseq in
    let r_cons = CP.has_tscons conseq in 
    let l_cons = CP.has_tscons ante in
    if r_cons = No_cons then
      if l_cons = No_cons then  x_add tp_imply_no_cache ante conseq imp_no timeout process
      else x_add tp_imply_no_cache (tpd_drop_all_perm ante) conseq imp_no timeout process
    else match join_res l_cons r_cons with
      | No_cons -> x_add tp_imply_no_cache ante conseq imp_no timeout process
      | No_split -> false
      | Can_split -> 
        let ante_lex, antes= CP.dnf_to_list ante in
        let conseq_lex, conseqs= CP.dnf_to_list conseq in
        let antes = List.map (fun a-> CP.tpd_drop_perm a, (ante_lex,CP.tpd_drop_nperm a)) antes in
        let conseqs = List.map (fun c-> CP.mkExists conseq_lex (CP.tpd_drop_perm c) None no_pos, (conseq_lex,CP.tpd_drop_nperm c)) conseqs in
        let tp_wrap fa fc = if CP.isConstTrue fc then true else x_add tp_imply_no_cache fa fc imp_no timeout process in
        let tp_wrap fa fc = Debug.no_2(* _loop *) "tp_wrap"  Cprinter.string_of_pure_formula  Cprinter.string_of_pure_formula string_of_bool tp_wrap fa fc in
        let ss_wrap (ea,fa) (ec,fc) = if fc=[] then true else Share_prover_w2.sleek_imply_wrapper (ea,fa) (ec,fc) in
        List.for_all( fun (npa,pa) -> List.exists (fun (npc,pc) -> tp_wrap npa npc && ss_wrap pa pc ) conseqs) antes
  else x_add tp_imply_no_cache ante conseq imp_no timeout process

let tp_imply_perm ante conseq imp_no timeout process =  
  let pr =  Cprinter.string_of_pure_formula in
  Debug.no_2(* _loop *) "tp_imply_perm" pr pr string_of_bool (fun _ _ -> tp_imply_perm ante conseq imp_no timeout process ) ante conseq

let imply_cache fn_imply ante conseq : bool  = 
  let () = Gen.Profiling.push_time_always "cache overhead" in
  let f = CP.mkOr conseq (CP.mkNot ante None no_pos) None no_pos in
  let sf = norm_var_name f in
  let prover = string_of_prover !pure_tp  in
  let fstring = Cprinter.string_of_pure_formula sf in
  let fstring_with_prover = prover^fstring in
  let () = cache_imply_count := !cache_imply_count+1 in
  let () = cache_status := true in
  let () = Gen.Profiling.pop_time_always "cache overhead" in
  let res =
    try
      find_cache !imply_cache fstring fstring_with_prover
      (* Hashtbl.find !imply_cache fstring *)
    with Not_found ->
      let () = cache_status := false in
      let r = fn_imply ante conseq in
      (* cache only sound outcomes : unless we add prover name to it *)
      let prover_str = if r then fstring else fstring_with_prover in
      let () = Gen.Profiling.push_time "cache overhead" in
      let () = cache_imply_miss := !cache_imply_miss+1 in
      let () = Hashtbl.add !imply_cache prover_str r in
      let () = Gen.Profiling.pop_time "cache overhead" in
      r
  in res

let imply_cache fn_imply ante conseq : bool  = 
  let pr = Cprinter.string_of_pure_formula in
  let pr2 b = ("found?:"^(string_of_bool !cache_status)
               ^" ans:"^(string_of_bool b)) in
  Debug.no_2 "imply_cache" pr pr pr2 (imply_cache fn_imply) ante conseq

let tp_imply ante conseq imp_no timeout process =
  (* TODO WN : can below remove duplicate constraints? *)
  (* let ante = CP.elim_idents ante in *)
  (* let conseq = CP.elim_idents conseq in *)
  let fn_imply a c = x_add_3 tp_imply_perm a c imp_no timeout process in
  (* let () = x_tinfo_hp (add_str "no-cache" string_of_bool) !Globals.no_cache_formula no_pos in *)
  if !Globals.no_cache_formula then
    fn_imply ante conseq
  else
    begin
      (* let () = x_tinfo_pp "prior to imply_cache"  no_pos in *)
      x_add_3 imply_cache fn_imply ante conseq
    end

(* (\*let () = Gen.Profiling.push_time "cache overhead" in*\) *)
(* let f = CP.mkOr conseq (CP.mkNot ante None no_pos) None no_pos in *)
(* let sf = norm_var_name f in *)
(* let fstring = Cprinter.string_of_pure_formula sf in *)
(* (\*let () = Gen.Profiling.pop_time "cache overhead" in*\) *)
(* let res =  *)
(*   try *)
(*     Hashtbl.find !imply_cache fstring *)
(*   with Not_found -> *)
(*     let r = tp_imply_perm ante conseq imp_no timeout process in *)
(*     (\*let () = Gen.Profiling.push_time "cache overhead" in*\) *)
(*     let () = Hashtbl.add !imply_cache fstring r in *)
(*     (\*let () = Gen.Profiling.pop_time "cache overhead" in*\) *)
(*     r *)
(* in res *)

let tp_imply ante conseq old_imp_no timeout process =	
  let imp_num = next_proof_no () in
  let imp_no = (string_of_int imp_num) in
  let imp_no = 
    if !Globals.imply_top_flag then imp_no^":"^old_imp_no 
    else imp_no
  in
  x_dinfo_zp (lazy ("IMP #" ^ imp_no)) no_pos;  
  x_dinfo_zp (lazy ("imply_timeout: ante: " ^ (!print_pure ante))) no_pos;
  x_dinfo_zp (lazy ("imply_timeout: conseq: " ^ (!print_pure conseq))) no_pos;
  let cmd = PT_IMPLY(ante,conseq) in
  let () = Log.last_proof_command # set cmd in
  let fn () = x_add tp_imply ante conseq imp_no timeout process in
  let logger fr tt timeout = 
    let tp = (string_of_prover !pure_tp) in
    let () =  add_proof_logging timeout !cache_status old_imp_no imp_num (string_of_prover !pure_tp) cmd tt 
        (match fr with Some b -> PR_BOOL b | None -> PR_exception) in
    (Others.last_tp_used # string_of,imp_no)
  in
  let final_res = Timelog.log_wrapper "imply" logger fn () in
  (* let _= add_proof_logging !cache_status old_imp_no imp_no (string_of_prover !pure_tp) cmd (Timelog.logtime # get_last_time) (PR_BOOL (match final_res with | r -> r))  *)
  final_res
;;

let tp_imply ante conseq imp_no timeout process =	
  let pr1 = Cprinter.string_of_pure_formula in
  let prout x = (last_prover())^": "^(string_of_bool x) in
  Debug.no_2 "tp_imply" 
    (add_str "ante" pr1) 
    (add_str "conseq" pr1) 
    (add_str "solver" prout) (fun _ _ -> tp_imply ante conseq imp_no timeout process) ante conseq


(* renames all quantified variables *)
let rec requant = function
  | CP.And (f, g, l) -> CP.And (requant f, requant g, l)
  | CP.AndList b -> CP.AndList (map_l_snd requant b)
  | CP.Or (f, g, lbl, l) -> CP.Or (requant f, requant g, lbl, l)
  | CP.Not (f, lbl, l) -> CP.Not (requant f, lbl, l)
  | CP.Forall (v, f, lbl, l) ->
    let nv = CP.fresh_spec_var v in
    CP.Forall (nv, (CP.subst [v, nv] (requant f)), lbl, l)
  | CP.Exists (v, f, lbl, l) ->
    let nv = CP.fresh_spec_var v in
    CP.Exists (nv, (CP.subst [v, nv] (requant f)), lbl, l)
  | x -> x
;;

let rewrite_in_list list formula =
  match formula with
  | CP.BForm ((CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _), _), _) ->
    List.map (fun x -> if x <> formula then CP.subst [v1, v2] x else x) list
  | CP.BForm ((CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _), _), _) ->
    List.map (fun x -> if x <> formula then CP.subst_term [v1, term] x else x) list
  | x -> list
;;

(*do not rewrite bag_vars*)
let rec rewrite_in_and_tree bag_vars rid formula rform =
  let rec helper rid formula rform =
    match formula with
    | CP.And (x, y, l) ->
      let (x, fx) = helper rid x rform in
      let (y, fy) = helper rid y rform in
      (CP.And (x, y, l), (fun e -> fx (fy e)))
    | CP.AndList b -> 
      let r1,r2 = List.fold_left (fun (a, f) (l,c)-> 
          let r1,r2 = helper rid c rform in
          (l,r1)::a, (fun e -> r2 (f e))) ([],(fun c-> c)) b in
      (AndList r1, r2)
    | x ->
      let subst_fun =
        match rform with
        | CP.BForm ((CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _), _), _) ->
          if (List.mem v1 bag_vars || (List.mem v2 bag_vars)) then  fun x -> x else
            CP.subst [v1, v2]
        | CP.BForm ((CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _), _), _) ->
          if (List.mem v1 bag_vars) then  fun x -> x else
            CP.subst_term [v1, term]
        | CP.BForm ((CP.Eq ((CP.IConst(i, _) as term), CP.Var (v1, _), _), _), _) ->
          if (List.mem v1 bag_vars) then  fun x -> x else
            CP.subst_term [v1, term]
        | _ -> fun x -> x
      in
      if ((not rid) && x = rform) then (x, subst_fun) else (subst_fun x, subst_fun)
  in helper rid formula rform
;;

let is_irrelevant = function
  | CP.BForm ((CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _), _), _) -> v1 = v2
  | CP.BForm ((CP.Eq (CP.IConst(i1, _), CP.IConst(i2, _), _), _), _) -> i1 = i2
  | _ -> false
;;

let rec get_rid_of_eq = function
  | CP.And (x, y, l) -> 
    if is_irrelevant x then (get_rid_of_eq y) else
    if is_irrelevant y then (get_rid_of_eq x) else
      CP.And (get_rid_of_eq x, get_rid_of_eq y, l)
  | CP.AndList b -> AndList (map_l_snd get_rid_of_eq b)
  | z -> z
;;

let rec fold_with_subst fold_fun current = function
  | [] -> current
  | h :: t ->
    let current, subst_fun = fold_fun current h in
    fold_with_subst fold_fun current (List.map subst_fun t)
;;

(* TODO goes in just once *)
(*do not simpl bag_vars*)
let rec simpl_in_quant formula negated rid =
  let bag_vars = CP.bag_vars_formula formula in
  let related_vars = List.map (fun v -> CP.find_closure_pure_formula v formula) bag_vars in
  let bag_vars = List.concat related_vars in
  let bag_vars = CP.remove_dups_svl bag_vars in
  let bag_vars = bag_vars@[(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in
  (* let () = print_endline (" ### bag_vars = " ^ (Cprinter.string_of_spec_var_list bag_vars)) in *)
  let rec helper formula negated rid = 
    match negated with
    | true ->
      begin match formula with
        | CP.Not (f, lbl, l) -> CP.Not (helper f false rid, lbl, l)
        | CP.Forall (v, f, lbl, l) -> CP.Forall (v, helper f true rid, lbl, l)
        | CP.Exists (v, f, lbl, l) -> CP.Exists (v, helper f true rid, lbl, l)
        | CP.Or (f, g, lbl, l) -> CP.mkOr (helper f false false) (helper g false false) lbl l
        | CP.And (_, _, _) ->
          let subfs = split_conjunctions formula in
          let nformula = fold_with_subst (rewrite_in_and_tree bag_vars rid) formula subfs in
          let nformula = get_rid_of_eq nformula in
          nformula
        | CP.AndList b -> AndList (map_l_snd (fun c-> helper c negated rid) b)
        | x -> x
      end
    | false ->
      begin match formula with
        | CP.Not (f, lbl, l) -> CP.Not (helper f true true, lbl, l)
        | CP.Forall (v, f, lbl, l) -> CP.Forall (v, helper f false rid, lbl, l)
        | CP.Exists (v, f, lbl, l) -> CP.Exists (v, helper f false rid, lbl, l)
        | CP.And (f, g, l) -> CP.And (helper f true false, helper g true false, l)
        | CP.AndList b -> AndList (map_l_snd (fun c-> helper c negated rid) b)
        | x -> x
      end
  in helper formula negated rid
;;

(* Why not used ?*)
let simpl_pair rid (ante, conseq) =
  (* let conseq_vars = CP.fv conseq in *)
  (* if (List.exists (fun v -> CP.name_of_spec_var v = waitlevel_name) conseq_vars) then *)
  (*   (ante,conseq) *)
  (* else *)
  let bag_vars = CP.bag_vars_formula ante in
  let bag_vars = bag_vars@[(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in
  let related_vars = List.map (fun v -> CP.find_closure_pure_formula v ante) bag_vars in
  let l1 = List.concat related_vars in
  let vars = CP.fv ante in
  let lock_vars = List.filter (fun v -> CP.type_of_spec_var v = lock_typ) vars in
  (*l1 is bag vars in both ante and conseq*)
  (*lock_vars are simplify*)
  let l1 = CP.remove_dups_svl (l1 @ (CP.bag_vars_formula conseq) @lock_vars) in
  (* let () = print_endline (" ### l1 = " ^ (Cprinter.string_of_spec_var_list l1)) in *)
  let antes = split_conjunctions ante in
  let fold_fun l_f_vars (ante, conseq)  = function
    | CP.BForm ((CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _), _), _) ->
      if (List.mem v1 l1 || (List.mem v2 l1)) then ((ante, conseq), fun x -> x) else
        ((CP.subst [v1, v2] ante, CP.subst [v1, v2] conseq), (CP.subst [v1, v2]))
    | CP.BForm ((CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _), _), _)
    | CP.BForm ((CP.Eq ((CP.IConst(i, _) as term), CP.Var (v1, _), _), _), _) ->
      if (List.mem v1 l1) then ((ante, conseq), fun x -> x)
      else ((CP.subst_term [v1, term] ante, CP.subst_term [v1, term] conseq), (CP.subst_term [v1, term]))
    | _ -> ((ante, conseq), fun x -> x)
  in
  let (ante1, conseq) = fold_with_subst (fold_fun l1) (ante, conseq) antes in
  let ante1 = get_rid_of_eq ante1 in
  (* let () = print_endline ("ante1 = " ^ (Cprinter.string_of_pure_formula ante1)) in *)
  let ante2 = simpl_in_quant ante1 true rid in
  (* let () = print_endline ("ante2 = " ^ (Cprinter.string_of_pure_formula ante2)) in *)
  let ante3 = simpl_in_quant ante2 true rid in
  (ante3, conseq)

let simpl_pair rid (ante, conseq) = (ante, conseq)

(* let simpl_pair rid (ante, conseq) = *)
(*   let pr_o = pr_pair Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula in *)
(*   Debug.no_2 "simpl_pair" *)
(*       Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula pr_o *)
(*       (fun _ _ -> simpl_pair rid (ante, conseq)) ante conseq *)

let simpl_pair rid (ante, conseq) =
  Gen.Profiling.do_1 "simpl_pair" (simpl_pair rid) (ante, conseq)
;;

let is_sat (f : CP.formula) (old_sat_no : string): bool =
  let f = elim_exists f in
  if (CP.isConstTrue f) then true 
  else if (CP.isConstFalse f) then false
  else
    let (f, _) = simpl_pair true (f, CP.mkFalse no_pos) in
    (* let f = CP.drop_rel_formula f in *)
    let res= sat_label_filter (fun c-> x_add tp_is_sat c old_sat_no) f in
    res
;;

let is_sat (f : CP.formula) (sat_no : string): bool =
  Debug.no_1 "is_sat_tp"  Cprinter.string_of_pure_formula string_of_bool (fun _ -> is_sat f sat_no) f


let imply_timeout_helper ante conseq process ante_inner conseq_inner imp_no timeout =  
  (* let ante0 = CP.infer_level_pure ante in *) (*add l.mu>0*) (*MERGE CHECK*)
  (* let conseq0 = CP.infer_level_pure conseq in *) (*add l.mu>0*) (*MERGE CHECK*)
  let acpairs = x_add imply_label_filter ante conseq in
  let pairs = List.map (fun (ante,conseq) -> 
      let () = x_dinfo_hp (add_str "ante 1: " Cprinter.string_of_pure_formula) ante no_pos in
      (* RHS split already done outside *)
      (* let cons = split_conjunctions conseq in *)
      let cons = [conseq] in
      List.map (fun cons-> 
          let (ante,cons) = simpl_pair false (requant ante, requant cons) in
          let () = x_dinfo_hp (add_str "ante 3: " Cprinter.string_of_pure_formula) ante no_pos in
          let ante = CP.remove_dup_constraints ante in
          let () = x_dinfo_hp (add_str "ante 4: " Cprinter.string_of_pure_formula) ante no_pos in
          match process with
          | Some (Some proc, true) -> (ante, cons) (* don't filter when in incremental mode - need to send full ante to prover *)
          | _ -> assumption_filter ante cons  ) cons) acpairs in
  let pairs = List.concat pairs in
  let pairs_length = List.length pairs in
  let () = (ante_inner := List.map fst pairs) in
  let () = (conseq_inner := List.map snd pairs) in
  let imp_sub_no = ref 0 in
  (* let () = (let () = print_string("\n!!!!!!! bef\n") in flush stdout ;) in *)
  let fold_fun (res1,res2,res3) (ante, conseq) =
    (incr imp_sub_no;
     if res1 then 
       let imp_no = 
         if pairs_length > 1 then ( (* let () = print_string("\n!!!!!!! \n") in flush stdout ; *) (imp_no ^ "." ^ string_of_int (!imp_sub_no)))
         else imp_no in
       (* (*DROP VarPerm formula before checking*)       *)
       (* let conseq = CP.drop_varperm_formula conseq in *)
       (* let ante = CP.drop_varperm_formula ante in     *)
       let res1 =
         if (not (CP.is_formula_arith ante))&& (CP.is_formula_arith conseq) then
           let res1 = x_add tp_imply(*_debug*) (CP.drop_bag_formula ante) conseq imp_no timeout process in
           if res1 then res1
           else x_add tp_imply(*_debug*) ante conseq imp_no timeout process
         else 
           x_add tp_imply(*_debug*) ante conseq imp_no timeout process 
       in
       let () = x_dinfo_hp (add_str "res: " string_of_bool) res1 no_pos in
       let l1 = CP.get_pure_label ante in
       let l2 = CP.get_pure_label conseq in
       if res1 then (res1,(l1,l2)::res2,None)
       else (res1,res2,l2)
     else 
       (res1,res2,res3) )
  in
  List.fold_left fold_fun (true,[],None) pairs;;


let imply_timeout (ante0 : CP.formula) (conseq0 : CP.formula) (old_imp_no : string) timeout process
  : bool*(formula_label option * formula_label option )list * (formula_label option) = (*result+successfull matches+ possible fail*)
  let (imp_num,old_imp_no) = 
    if !Globals.imply_top_flag 
    then
      begin
        let pno = next_proof_no () in
        (pno,string_of_int pno)
      end
    else (0,old_imp_no)
  in
  (* let count_inner = ref 0 in *)
  let imp_no = old_imp_no in
  let ante_inner = ref [] in
  let conseq_inner = ref [] in
  (* let tstart = Gen.Profiling.get_time () in		 *)
  (* x_dinfo_zp (lazy ("IMP #" ^ imp_no)) no_pos;   *)
  (* x_dinfo_zp (lazy ("imply_timeout: ante: " ^ (!print_pure ante0))) no_pos; *)
  (* x_dinfo_zp (lazy ("imply_timeout: conseq: " ^ (!print_pure conseq0))) no_pos; *)
  let cmd = PT_IMPLY_TOP(ante0,conseq0) in
  (* let () = Log.last_proof_command # set cmd in *)
  let fn () =
    if !external_prover then 
      match Netprover.call_prover (Imply (ante0,conseq0)) with
        Some res -> (res,[],None)       
      | None -> (false,[],None)
    else begin
      let ante0,conseq0 = if (!Globals.allow_locklevel) then
          (*should translate waitlevel before level*)
          let ante0 = CP.translate_waitlevel_pure ante0 in
          let ante0 = CP.translate_level_pure ante0 in
          let conseq0 = CP.translate_waitlevel_pure conseq0 in
          let conseq0 = CP.translate_level_pure conseq0 in
          let () = x_dinfo_hp (add_str "After translate_: ante0 = " Cprinter.string_of_pure_formula) ante0 no_pos in
          let () = x_dinfo_hp (add_str "After translate_: conseq0 = " Cprinter.string_of_pure_formula) conseq0 no_pos in
          (ante0,conseq0)
        else 
          (* let ante0 = CP.drop_svl_pure ante0 [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in *)
          (* let ante0 = CP.drop_locklevel_pure ante0 in *)
          (* let conseq0 = CP.drop_svl_pure conseq0 [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in *)
          (* let conseq0 = CP.drop_locklevel_pure conseq0 in *)
          (ante0,conseq0)
      in

      let conseq = if CP.should_simplify conseq0 then simplify_a 12 conseq0 else conseq0 in
      (*let () = print_string ("imply_timeout: new_conseq: " ^ (Cprinter.string_of_pure_formula conseq) ^ "\n") in*)
      if CP.isConstTrue conseq then (true, [],None)
      else
        let ante = if CP.should_simplify ante0 then simplify_a 13 ante0 else ante0 in
        if (* CP.isConstFalse ante0 || *) CP.isConstFalse ante then (true,[],None)
        else
          let ante = elim_exists ante in
          let conseq = elim_exists conseq in
          (*let () = print_string ("imply_timeout: new_conseq: " ^ (Cprinter.string_of_pure_formula conseq) ^ "\n") in*)
          (*if no_andl conseq || *)
          if (CP.rhs_needs_or_split conseq)&& not (no_andl ante) && !label_split_conseq then
            let conseq_disj = CP.split_disjunctions conseq in
            List.fold_left (fun (r1,r2,r3) d -> 
                if not r1 then x_add imply_timeout_helper ante d process ante_inner conseq_inner imp_no timeout
                else (r1,r2,r3) ) (false,[],None) conseq_disj 
          else imply_timeout_helper ante conseq process ante_inner conseq_inner imp_no timeout
    end;
  in 
  let final_res = (* Timelog.logtime_wrapper "imply" *) fn () in
  (* let tstop = Gen.Profiling.get_time () in *)
  (* let () = print_string ("length of pairs: "^(string_of_int (List.length !ante_inner))) in *)
  (* let ante0 = CP.join_conjunctions !ante_inner in *)
  (* let conseq0 = CP.join_conjunctions !conseq_inner in *)
  (* let () = Log.last_cmd # dumping imp_no in *)
  if !Globals.imply_top_flag then
    add_proof_logging false false old_imp_no imp_num "funny" cmd (* (PT_IMPLY (ante0, conseq0)) *) (Timelog.logtime # get_last_time) (PR_BOOL (match final_res with | r,_,_ -> r));
  final_res
;;

let imply_timeout (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout process
  : bool*(formula_label option * formula_label option )list * (formula_label option) (*result+successfull matches+ possible fail*)
  = let pf = Cprinter.string_of_pure_formula in
  (*let () = print_string "dubios!!\n" in*)
  Debug.no_2 "imply_timeout 1" pf pf (fun (b,_,_) -> string_of_bool b)
    (fun a c -> imply_timeout a c imp_no timeout process) ante0 conseq0

let univ_rhs_store = 
object (self)
  val super = new store (CP.mkTrue no_pos) !CP.print_formula
  method set a =
    if super # is_empty then super # set a
    else
      let old = super # get in
      super # set (CP.mkAnd a old no_pos)
      (* failwith (x_loc^"over-writing "^old) *)
  method is_empty = super # is_empty
  method get_rm = super # get_rm
  method get = super # get
  method reset = super # get_rm
end

(* this help remove univ_rhs at the end of method *)
let wrap_remove_univ_rhs f x =
  try
    let r = f x in
    let _ = univ_rhs_store # reset in
    r
  with e ->
    let _ = univ_rhs_store # reset in
    raise e

let get_univs_from_ante ante =
  let univ_vars = CP.get_RelForm_arg_list_with_name ante "Univ" in
  if univ_vars==[] then []
  else
    (*Is it correct to make all the variables equal to m universal?*)
    let () = y_dinfo_hp (add_str "get_univs_from_ante" (pr_list !CP.print_sv)) univ_vars in
    let eqns' = MCP.ptr_equations_without_null (MCP.mix_of_pure ante) in
    let emap = CP.EMapSV.build_eset eqns' in
    let univ_vars2 = List.concat (List.map (fun x -> CP.EMapSV.find_equiv_all x emap) univ_vars)@univ_vars in
    univ_vars2


let connected_rhs univ_vars rhs =
  if univ_vars==[] then false
  else
    let vs= CP.fv rhs in
    (CP.intersect_svl univ_vars vs)!=[]

let connected_rhs univ_vars rhs =
  Debug.no_2 "connected_rhs" (pr_list !CP.print_sv) !CP.print_formula string_of_bool connected_rhs univ_vars rhs
;;

let filter_inv ante =
  let conjs = CP.split_conjunctions ante in
  let conjs = List.filter (fun f -> not(CP.is_Or f)) conjs in
  CP.join_conjunctions conjs

let filter_inv ante =
  let pr = !CP.print_formula in
  Debug.no_1 "filter_inv" pr pr filter_inv ante

let imply_timeout_univ univ_vars ante0 conseq0 imp_no timeout process =
    let () = y_dinfo_pp "Processing univ instantiation" in
    let () = y_dinfo_hp (add_str "univ var" (pr_list !CP.print_sv)) univ_vars in
    let () = y_dinfo_hp (add_str "ante0" !CP.print_formula) ante0 in
    let () = y_dinfo_hp (add_str "conseq0" !CP.print_formula) conseq0 in
    let prev_inst = univ_rhs_store # get in
    let () = y_dinfo_hp (add_str "prev_inst" !CP.print_formula) prev_inst in
    let ante0 = CP.drop_rel_formula ante0 in
    let ante1 = filter_inv ante0 in
    let () = y_dinfo_hp (add_str "ante1 (aftre filter inv)" !CP.print_formula) ante1 in
    let new_conseq = CP.mkAnd ante1 prev_inst no_pos in
    (* let () = y_tinfo_hp (add_str "univ_vars2" (pr_list !CP.print_sv)) univ_vars in *)
    let new_conseq = CP.mkAnd new_conseq conseq0 no_pos in
    let new_conseq = CP.mkExists univ_vars new_conseq None no_pos in
    let () = y_dinfo_hp (add_str "new_conseq" !CP.print_formula) new_conseq in
    let (b,_,_) as r = x_add imply_timeout ante0 new_conseq imp_no timeout process in
    let () = y_dinfo_hp (add_str "imply_timeout_univ: b " string_of_bool) b in
    if b then
      let () = univ_rhs_store # set conseq0 in r
    else r


let imply_timeout ante0 conseq0 imp_no timeout process =
  let (b,lst,fl) as ans = x_add imply_timeout ante0 conseq0 imp_no timeout process in
  let univ_vars = get_univs_from_ante ante0 in
  let () = y_dinfo_hp (add_str "univ var" (pr_list !CP.print_sv)) univ_vars in
  if (not b) && (connected_rhs univ_vars conseq0)
  then imply_timeout_univ univ_vars ante0 conseq0 imp_no timeout process
  else ans
;;
  
let imply_timeout (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout process
  : bool*(formula_label option * formula_label option )list * (formula_label option) (*result+successfull matches+ possible fail*)
  = let pf = Cprinter.string_of_pure_formula in
  (*let () = print_string "dubios!!\n" in*)
  Debug.no_2 "imply_timeout 2" pf pf (fun (b,_,_) -> string_of_bool b)
    (fun a c -> imply_timeout a c imp_no timeout process) ante0 conseq0


(* let imply_timeout_slicing (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout process *)
(* 	: bool*(formula_label option * formula_label option )list * (formula_label option) = (\*result+successfull matches+ possible fail*\) *)
(*   (\* let () = print_string ("\nTpdispatcher.ml: imply_timeout begining") in *\) *)
(*   proof_no := !proof_no + 1 ;  *)
(*   let imp_no = (string_of_int !proof_no) in *)
(*   (\* let () = print_string ("\nTPdispatcher.ml: imply_timeout:" ^ imp_no) in *\) *)
(*   x_dinfo_zp (lazy ("IMP #" ^ imp_no)) no_pos;   *)
(*   x_dinfo_zp (lazy ("ante: " ^ (!print_pure ante0))) no_pos; *)
(*   x_dinfo_zp (lazy ("conseq: " ^ (!print_pure conseq0))) no_pos; *)
(*   if !external_prover then  *)
(*     match Netprover.call_prover (Imply (ante0,conseq0)) with *)
(*       | Some res -> (res,[],None)        *)
(* 	  | None -> (false,[],None) *)
(*   else begin  *)
(* 	(\*let () = print_string ("Imply: => " ^(Cprinter.string_of_pure_formula ante0)^"\n==> "^(Cprinter.string_of_pure_formula conseq0)^"\n") in*\) *)
(* 	let conseq = if CP.should_simplify conseq0 then simplify_a 12 conseq0 else conseq0 in (\* conseq is Exists formula *\) *)
(* 	(\*let () = print_string ("imply_timeout: new_conseq: " ^ (Cprinter.string_of_pure_formula conseq) ^ "\n") in*\) *)
(* 	if CP.isConstTrue conseq then (true, [], None) *)
(* 	else *)
(* 	  let ante = if CP.should_simplify ante0 then simplify_a 13 ante0 else ante0 in *)
(* 	  (\*let () = print_string ("imply_timeout: new_ante: " ^ (Cprinter.string_of_pure_formula ante) ^ "\n") in*\) *)
(* 	  if CP.isConstFalse ante then (true, [], None) *)
(* 	  else *)
(*         (\* let () = print_string ("\nTpdispatcher.ml: imply_timeout bef elim exist ante") in *\) *)
(* 		let ante = elim_exists ante in *)
(*         (\* let () = print_string ("\nTpdispatcher.ml: imply_timeout after elim exist ante") in *\) *)
(* 		let conseq = elim_exists conseq in *)
(* let conseq0 = CP.drop_svl_pure conseq0 [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in *)
(* let conseq0 = CP.drop_locklevel_pure conseq0 in *)
(*       (ante0,conseq0) *)
(* in *)



(* 		(\*let () = print_string ("imply_timeout: new_conseq: " ^ (Cprinter.string_of_pure_formula conseq) ^ "\n") in*\) *)

(*         (\* A1 -> B => A1 /\ A2 => B *\) *)
(* 		(\* A1 is (filter A1 /\ A2)  *\) *)
(* 		let imply_conj_lhs ante conseq = *)
(* 		  let conseq = if CP.should_simplify conseq then simplify_a 14 conseq else conseq in *)
(* 		  if CP.isConstTrue conseq then (true, [], None) *)
(* 		  else *)
(* 			let ante = if CP.should_simplify ante then simplify_a 15 ante else ante in *)
(* 			if CP.isConstFalse ante then (true, [], None) *)
(* 			else *)
(* 			  let (ante, cons) = simpl_pair false (requant ante, requant conseq) in  *)
(* 			  let ante = CP.remove_dup_constraints ante in *)
(* 			  let (ante, cons) = match process with *)
(* 				| Some (Some proc, true) -> (ante, cons) (\* don't filter when in incremental mode - need to send full ante to prover *\) *)
(* 				| _ -> assumption_filter ante cons in *)
(* 			  let cons = CP.drop_varperm_formula cons in *)
(*               let ante = CP.drop_varperm_formula ante in *)
(* 			  let res = *)
(* 				if (not (CP.is_formula_arith ante)) && (CP.is_formula_arith cons) then *)
(* 				  let res = tp_imply (CP.drop_bag_formula ante) cons imp_no timeout process in *)
(* 				  if res then res *)
(* 				  else tp_imply ante cons imp_no timeout process *)
(* 				else tp_imply ante cons imp_no timeout process *)
(* 			  in *)
(*  			  let l1 = CP.get_pure_label ante in *)
(*               let l2 = CP.get_pure_label cons in *)
(* 			  if res then (res, [(l1,l2)], None) *)
(* 			  else (res, [], l2) *)
(* 		in *)

(* 		let imply_conj_lhs ante conseq = *)
(* 		  let pr = Cprinter.string_of_pure_formula in *)
(* 		  Debug.no_2 "imply_timeout: imply_conj_lhs" pr pr *)
(* 			(fun (r, _, _) -> string_of_bool r) imply_conj_lhs ante conseq *)
(* 		in *)

(* 		(\* A \/ B -> C <=> (A -> C) /\ (B -> C) *\) *)
(* 		let imply_disj_lhs ante conseq = *)
(* 		  let ante = x_add CP.elim_exists_with_simpl simplify ante in *)
(* 		  let _,l_ante = CP.dnf_to_list ante in *)
(* 		  let pairs = List.map (fun ante -> (ante, conseq)) l_ante in *)
(* 		  let fold_fun (res1, res2, res3) (ante, cons) = *)
(* 			if res1 then *)
(* 			  let (r1, r2, r3) = imply_conj_lhs ante cons in *)
(* 			  if r1 then (r1, r2@res2, None) *)
(* 			  else (r1, res2, r3) *)
(* 			else (res1, res2, res3) *)
(* 		  in *)
(* 		  List.fold_left fold_fun (true, [], None) pairs *)
(* 		in *)

(* 	    (\* A -> B /\ C <=> (A -> B) /\ (A -> C) *\) *)
(* 		let imply_conj_rhs ante conseq =  *)
(* 		  let split_conseq = split_conjunctions conseq in *)
(* 		  let pairs = List.map (fun cons -> (ante, cons)) split_conseq in *)
(* 		  let fold_fun (res1, res2, res3) (ante, cons) = *)
(* 			if res1 then *)
(* 			  let (r1, r2, r3) = imply_disj_lhs ante cons in *)
(* 			  if r1 then (r1, r2@res2, None) *)
(* 			  else (r1, res2, r3) *)
(* 			else (res1, res2, res3) *)
(* 		  in *)
(* 		  List.fold_left fold_fun (true, [], None) pairs *)
(* 		in *)

(* 		(\* A -> B \/ C <=> (A -> B) \/ (A -> C) *\) *)
(* 		let imply_disj_rhs ante conseq = *)
(* 		  let cons = x_add CP.elim_exists_with_simpl simplify conseq in *)
(* 		  let _,l_cons = CP.dnf_to_list cons in (\* Transform conseq into DNF *\) *)
(* 		  let pairs = List.map (fun cons -> (ante, cons)) l_cons in *)
(* 		  let fold_fun (res1, res2, res3) (ante, cons) = *)
(* 			if not res1 then *)
(* 			  let (r1, r2, r3) = imply_conj_rhs ante cons in *)
(* 			  (r1, r2@res2, r3) (\* Should store r3 as a list of failure reason *\) *)
(* 			else (res1, res2, res3) *)
(* 		  in *)
(* 		  List.fold_left fold_fun (false, [], None) pairs *)
(* 		in *)
(* 		imply_disj_rhs ante conseq *)
(*   end; *)
(* ;; *)

let imply_timeout (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout do_cache process
  : bool*(formula_label option * formula_label option )list * (formula_label option) =
  (* if !do_slicing && !multi_provers then                      *)
  (* imply_timeout_slicing ante0 conseq0 imp_no timeout process *)
  (* else                                                       *)
  (* imply_timeout ante0 conseq0 imp_no timeout process         *)
  x_add imply_timeout ante0 conseq0 imp_no timeout process


let imply_timeout (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout do_cache process
  : bool*(formula_label option * formula_label option )list * (formula_label option) (*result+successfull matches+ possible fail*)
  = let pf = Cprinter.string_of_pure_formula in
  let prf = add_str "timeout" string_of_float in
  let nxt = get_proof_no ()+1 in
  Debug.no_4 "imply_timeout 3" pf pf prf pr_id (fun (b,_,_) -> string_of_bool b)
    (fun a c _ _ -> imply_timeout a c imp_no timeout do_cache process) ante0 conseq0 timeout (string_of_int nxt)

let imply_timeout ante0 conseq0 imp_no timeout do_cache process =
  let s = "imply" in
  let () = Gen.Profiling.push_time s in
  let (res1,res2,res3) = x_add imply_timeout ante0 conseq0 imp_no timeout do_cache process in
  let () = Gen.Profiling.pop_time s in
  if res1  then Gen.Profiling.inc_counter "true_imply_count" else Gen.Profiling.inc_counter "false_imply_count" ; 
  (res1,res2,res3)

let imply_timeout a c i t dc process =
  disj_cnt a (Some c) "imply";
  Gen.Profiling.do_5 "TP.imply_timeout" imply_timeout a c i t dc process

let memo_imply_timeout ante0 conseq0 imp_no timeout = 
  (* let () = print_string ("\nTPdispatcher.ml: memo_imply_timeout") in *)
  let () = Gen.Profiling.push_time "memo_imply" in
  let r = List.fold_left (fun (r1,r2,r3) c->
      if not r1 then (r1,r2,r3)
      else
        let l = List.filter (fun d -> (List.length (Gen.BList.intersect_eq CP.eq_spec_var c.memo_group_fv d.memo_group_fv))>0) ante0 in
        let ant = MCP.fold_mem_lst_m (CP.mkTrue no_pos) true (*!no_LHS_prop_drop*) true l in
        let con = MCP.fold_mem_lst_m (CP.mkTrue no_pos) !no_RHS_prop_drop false [c] in
        let r1',r2',r3' = x_add imply_timeout ant con imp_no timeout false None in 
        (r1',r2@r2',r3')) (true, [], None) conseq0 in
  let () = Gen.Profiling.pop_time "memo_imply" in
  r

let memo_imply_timeout ante0 conseq0 imp_no timeout =
  Debug.no_2 "memo_imply_timeout"
    (Cprinter.string_of_memoised_list)
    (Cprinter.string_of_memoised_list)
    (fun (r,_,_) -> string_of_bool r)
    (fun a c -> memo_imply_timeout a c imp_no timeout) ante0 conseq0

let mix_imply_timeout ante0 conseq0 imp_no timeout =
  match ante0,conseq0 with
  | MCP.MemoF a, MCP.MemoF c -> memo_imply_timeout a c imp_no timeout
  | MCP.OnePF a, MCP.OnePF c -> x_add imply_timeout a c imp_no timeout false None
  | _ -> report_error no_pos ("mix_imply_timeout: mismatched mix formulas ")

let mix_imply_timeout ante0 conseq0 imp_no timeout =
  Debug.no_2 "mix_imply_timeout"
    (Cprinter.string_of_mix_formula)
    (Cprinter.string_of_mix_formula)
    (fun (r,_,_) -> string_of_bool r)
    (fun a c -> mix_imply_timeout a c imp_no timeout) ante0 conseq0

let rec imply_one i ante0 conseq0 imp_no do_cache process =
  (* let () = print_endline "inside imply_one" in *)
  Debug.no_2(* _num i *) "imply_one" (Cprinter.string_of_pure_formula) 
    (Cprinter.string_of_pure_formula)
    (fun (r, _, _) -> string_of_bool r)
    (fun ante0 conseq0 -> imply_x ante0 conseq0 imp_no do_cache process) ante0 conseq0

and imply_x ante0 conseq0 imp_no do_cache process = x_add imply_timeout ante0 conseq0 imp_no !imply_timeout_limit do_cache process ;;

let simpl_imply_raw_x ante conseq =
  let (r,_,_)= x_add imply_one 0 ante conseq "0" false None in
  r

let simpl_imply_raw ante conseq =
  Debug.no_2 "simpl_imply_raw" (Cprinter.string_of_pure_formula)(Cprinter.string_of_pure_formula) string_of_bool
    simpl_imply_raw_x ante conseq

let memo_imply ante0 conseq0 imp_no = x_add memo_imply_timeout ante0 conseq0 imp_no !imply_timeout_limit ;;

let mix_imply ante0 conseq0 imp_no = x_add mix_imply_timeout ante0 conseq0 imp_no !imply_timeout_limit ;;

let mix_imply ante0 conseq0 imp_no =
  Debug.no_3 "mix_imply"
    (Cprinter.string_of_mix_formula)
    (Cprinter.string_of_mix_formula) pr_id
    (fun (r,_,_) -> string_of_bool r)
    mix_imply ante0 conseq0 imp_no

(* CP.formula -> string -> 'a -> bool *)
let is_sat f sat_no do_cache =
  if !external_prover then
    match Netprover.call_prover (Sat f) with
      Some res -> res
    | None -> false
  else  begin
    disj_cnt f None "sat";
    Gen.Profiling.do_1 "is_sat" (is_sat f) sat_no
  end
;;

let is_sat i f sat_no do_cache =
  Debug.no_1_num i "is_sat" Cprinter.string_of_pure_formula string_of_bool (fun _ -> is_sat f sat_no do_cache) f


let sat_no = ref 1 ;;

let incr_sat_no () =  sat_no := !sat_no +1  ;;

let is_sat_sub_no_c (f : CP.formula) sat_subno do_cache : bool = 
  let sat = is_sat 1 f ((string_of_int !sat_no) ^ "." ^ (string_of_int !sat_subno)) do_cache in
  sat_subno := !sat_subno+1;
  sat
;;

let is_sat_sub_no_c i (f : CP.formula) sat_subno do_cache : bool =
  Debug.no_1_num i "is_sat_sub_no_c" Cprinter.string_of_pure_formula string_of_bool (fun f -> is_sat_sub_no_c f sat_subno do_cache) f
;;

let is_sat_sub_no_with_slicing_orig (f:CP.formula) sat_subno : bool =  
  let rec group_conj l = match l with
    | [] -> (false,[]) 
    | (fvs, fs)::t ->  
      let b,l = group_conj t in
      let l1,l2 = List.partition (fun (c,_)-> not((Gen.BList.intersect_eq CP.eq_spec_var fvs c)==[])) l in
      if l1==[] then (b,(fvs,fs)::l) 
      else 
        let vars,nfs = List.split l1 in 
        let nfs = CP.join_conjunctions (fs::nfs) in
        let nvs = CP.remove_dups_svl (List.concat (fvs::vars)) in
        (true,(nvs,nfs)::l2) in

  let rec fix n_l = 
    let r1,r2 = group_conj n_l in
    if r1 then fix r2 else r2 in    
  let split_sub_f f = 
    let conj_list = CP.split_conjunctions f in
    let n_l = List.map (fun c-> (CP.fv c , c)) conj_list in
    snd (List.split (fix n_l)) in
  let  n_f_l = split_sub_f f in
  List.fold_left (fun a f -> if not a then a else is_sat_sub_no_c 1 f sat_subno false) true n_f_l 

let is_sat_sub_no_slicing (f:CP.formula) sat_subno : bool =
  let overlap (nlv1, lv1) (nlv2, lv2) =
    if (nlv1 = [] && nlv2 = []) then (Gen.BList.list_equiv_eq CP.eq_spec_var lv1 lv2)
    else (Gen.BList.overlap_eq CP.eq_spec_var nlv1 nlv2)
  in

  let rec group_conj l = match l with
    | [] -> (false,[]) 
    | ((f_nlv, f_lv), fs)::t ->  
      let b,l = group_conj t in
      let l1, l2 = List.partition (fun (cfv, _) -> overlap (f_nlv, f_lv) cfv) l in
      if l1==[] then (b,((f_nlv, f_lv), fs)::l) 
      else 
        let l_fv, nfs = List.split l1 in
        let l_nlv, l_lv = List.split l_fv in
        let nfs = CP.join_conjunctions (fs::nfs) in
        let n_nlv = CP.remove_dups_svl (List.concat (f_nlv::l_nlv)) in
        let n_lv = CP.remove_dups_svl (List.concat (f_lv::l_lv)) in
        (true,((n_nlv, n_lv), nfs)::l2)
  in

  let rec fix n_l = 
    let r1, r2 = group_conj n_l in
    if r1 then fix r2 else r2
  in    

  let split_sub_f f = 
    let conj_list = CP.split_conjunctions f in
    let n_l = List.map
        (fun c -> (CP.fv_with_slicing_label c, c)) conj_list in
    snd (List.split (fix n_l))
  in

  let n_f = (*CP.elim_exists_with_fresh_vars*) x_add CP.elim_exists_with_simpl simplify f in
  let dnf_f = snd (CP.dnf_to_list n_f) in

  let is_related f1 f2 =
    let (nlv1, lv1) = CP.fv_with_slicing_label f1 in
    let fv = CP.fv f2 in
    if (nlv1 == []) then Gen.BList.overlap_eq CP.eq_spec_var fv lv1
    else Gen.BList.overlap_eq CP.eq_spec_var fv nlv1
  in 

  let pick_rel_constraints f f_l = List.find_all (fun fs -> fs != f && is_related fs f) f_l in 

  (* SAT(A /\ B) = SAT(A) /\ SAT(B) if fv(A) and fv(B) are disjointed (auto-slicing) *)
  let check_sat f =
    let n_f_l = split_sub_f f in
    List.fold_left (fun a f ->
        if not a then a
        else is_sat_sub_no_c 2 (CP.join_conjunctions (f::(pick_rel_constraints f n_f_l))) sat_subno false) true n_f_l
  in

  (* SAT(A \/ B) = SAT(A) \/ SAT(B) *)

  List.fold_left (fun a f -> if a then a else check_sat f) false dnf_f

let is_sat_sub_no_slicing (f:CP.formula) sat_subno : bool =
  Debug.no_1 "is_sat_sub_no_with_slicing"
    Cprinter.string_of_pure_formula
    string_of_bool
    (fun f -> is_sat_sub_no_slicing f sat_subno) f

let is_sat_sub_no (f : CP.formula) sat_subno : bool =
  if !is_sat_slicing then is_sat_sub_no_slicing f sat_subno
  (* else if !do_slicing && !multi_provers then is_sat_sub_no_slicing f sat_subno *)
  else is_sat_sub_no_c 3 f sat_subno false

let is_sat_sub_no i (f : CP.formula) sat_subno : bool =
  Debug.no_2_num i "is_sat_sub_no " (Cprinter.string_of_pure_formula) (fun x-> string_of_int !x)
    (string_of_bool ) is_sat_sub_no f sat_subno;;

let is_sat_memo_sub_no_orig (f : memo_pure) sat_subno with_dupl with_inv : bool =
  if !f_2_slice || !dis_slicing then
    let f_lst = MCP.fold_mem_lst_to_lst f with_dupl with_inv true in
    (is_sat_sub_no 1 (CP.join_conjunctions f_lst) sat_subno)
  else if (MCP.isConstMFalse (MemoF f)) then false
  else
    (* let f = if !do_slicing                            *)
    (* 	(* Slicing: Only check changed slice *)          *)
    (* 	then List.filter (fun c -> c.memo_group_unsat) f *)
    (* 	else f in                                        *)
    let f_lst = MCP.fold_mem_lst_to_lst f with_dupl with_inv true in
    not (List.exists (fun f -> not (is_sat_sub_no 2 f sat_subno)) f_lst)

let is_sat_memo_sub_no_orig (f : memo_pure) sat_subno with_dupl with_inv : bool =
  Debug.no_1 "is_sat_memo_sub_no_orig"
    Cprinter.string_of_memo_pure_formula
    string_of_bool
    (fun _ -> is_sat_memo_sub_no_orig f sat_subno with_dupl with_inv) f

let is_sat_memo_sub_no_slicing (f : memo_pure) sat_subno with_dupl with_inv : bool =
  if (not (is_sat_memo_sub_no_orig f sat_subno with_dupl with_inv)) then (* One slice is UNSAT *) false
  else (* Improve completeness of SAT checking *)
    let f_l = MCP.fold_mem_lst_to_lst_gen_for_sat_slicing f with_dupl with_inv true true in
    not (List.exists (fun f -> not (is_sat_sub_no 3 f sat_subno)) f_l)

let is_sat_memo_sub_no_slicing (f : memo_pure) sat_subno with_dupl with_inv : bool =
  Debug.no_1 "is_sat_memo_sub_no_slicing"
    Cprinter.string_of_memo_pure_formula
    string_of_bool
    (fun _ -> is_sat_memo_sub_no_slicing f sat_subno with_dupl with_inv) f

let rec is_sat_memo_sub_no_ineq_slicing (mem : memo_pure) sat_subno with_dupl with_inv : bool =
  Debug.no_1 "is_sat_memo_sub_no_ineq_slicing"
    Cprinter.string_of_memo_pure_formula
    string_of_bool
    (fun mem -> is_sat_memo_sub_no_ineq_slicing_x2 mem sat_subno with_dupl with_inv) mem

and is_sat_memo_sub_no_ineq_slicing_x1 (mem : memo_pure) sat_subno with_dupl with_inv : bool =
  let is_sat_one_slice mg =
    if (MCP.is_ineq_linking_memo_group mg)
    then (* mg is a linking inequality *)
      true
    else
      let aset = mg.memo_group_aset in
      let apart = EMapSV.partition aset in
      (* let r = List.fold_left (fun acc p -> if acc then acc else MCP.exists_contradiction_eq mem p) false apart in *)
      let r = List.exists (fun p -> MCP.exists_contradiction_eq mem p) apart in
      if r then false (* found an equality contradiction *)
      else
        let related_ineq = List.find_all (fun img ->
            (MCP.is_ineq_linking_memo_group img) && 
            (Gen.BList.subset_eq eq_spec_var img.memo_group_fv mg.memo_group_fv)) mem in
        let f = join_conjunctions (MCP.fold_mem_lst_to_lst (mg::related_ineq) with_dupl with_inv true) in
        is_sat_sub_no 4 f sat_subno
  in
  (* List.fold_left (fun acc mg -> if not acc then acc else is_sat_one_slice mg) true mem *)
  not (List.exists (fun mg -> not (is_sat_one_slice mg)) mem)

and is_sat_memo_sub_no_ineq_slicing_x2 (mem : memo_pure) sat_subno with_dupl with_inv : bool =
  let is_sat_one_slice mg =
    if (MCP.is_ineq_linking_memo_group mg)
    then (* mg is a linking inequality *)
      true
    else
      let related_ineq = List.find_all (fun img ->
          (MCP.is_ineq_linking_memo_group img) && 
          (Gen.BList.subset_eq eq_spec_var img.memo_group_fv mg.memo_group_fv)) mem in
      let f = join_conjunctions (MCP.fold_mem_lst_to_lst (mg::related_ineq) with_dupl with_inv true) in
      is_sat_sub_no 5 f sat_subno
  in
  (* List.fold_left (fun acc mg -> if not acc then acc else is_sat_one_slice mg) true mem *)
  not (List.exists (fun mg -> not (is_sat_one_slice mg)) mem)

(* and is_sat_memo_sub_no_ineq_slicing_x2 (mem : memo_pure) sat_subno with_dupl with_inv : bool =                                            *)
(*   (* Aggressive search on inequalities *)                                                                                                 *)
(*   let is_sat_one_slice mg (kb : (bool option * memoised_group) list) =                                                                    *)
(* 	if (MCP.is_ineq_linking_memo_group mg)                                                                                                  *)
(* 	then (* mg is a linking inequality *)                                                                                                   *)
(* 	  (* For each fv v of a linking ineq, find all other slices that relates to v *)                                                        *)

(* 	  let () = print_string ("\nis_sat_memo_sub_no_ineq_slicing_x2: ineq: " ^ (Cprinter.string_of_spec_var_list mg.memo_group_fv) ^ "\n") in *)

(* 	  (* Find slices which contain both free vars of ineq and                                                                               *)
   (* 		 try to discover contradictory cycle in those slices first *)                                                                         *)
(* 	  let (d_kb, s_kb) = List.partition (fun (_, s) ->                                                                                      *)
(* 		(s != mg) && (Gen.BList.subset_eq eq_spec_var mg.memo_group_fv s.memo_group_fv)) kb in                                                *)

(* 	  let res = List.fold_left (fun a_r (_, s) ->                                                                                           *)
(* 		if not a_r then a_r                                                                                                                   *)
(* 		else                                                                                                                                  *)
(* 		  let aset = s.memo_group_aset in                                                                                                     *)
(* 		  let apart = EMapSV.partition aset in                                                                                                *)
(* 		  (* r = true -> a contradictory cycle is found *)                                                                                    *)
(* 		  let r = List.fold_left (fun acc p -> if acc then acc else MCP.exists_contradiction_eq mem p) false apart in                         *)
(* 		  not r                                                                                                                               *)
(* 	  ) true d_kb in                                                                                                                        *)

(* 	  if not res then (res, kb)                                                                                                             *)
(* 	  else                                                                                                                                  *)

(* 		let (related_slices, unrelated_slices) = List.fold_left (fun (a_rs, a_urs) v ->                                                       *)
(* 		  let (v_rs, v_urs) = List.partition (fun (_, s) -> (* No overlapping slices btw variables *)                                         *)
(* 			(s != mg) &&                                                                                                                        *)
(* 			  (List.mem v s.memo_group_fv) &&                                                                                                   *)
(* 			  not (MCP.is_ineq_linking_memo_group s)                                                                                            *)
(* 		  ) a_urs in (v_rs::a_rs, v_urs)                                                                                                      *)
(* 		) ([], s_kb) mg.memo_group_fv in                                                                                                      *)

(* 		let () = print_string ("\nis_sat_memo_sub_no_ineq_slicing_x2: related_slices: " ^                                                      *)
(* 								 (pr_list (fun l_x -> pr_list (fun (_, x) -> Cprinter.string_of_memoised_group x) l_x) related_slices)) in                *)

(* 	    (* Filter slices without relationship, for example, keep x<=z and z<=y for x!=y *)                                                  *)
(* 		let rec filter_slices (l_l_slices : (bool * (bool option * memoised_group)) list list) = (* (is_marked, (is_sat, slice)) *)           *)
(* 		(* Only work if the initial size of ll_slices is 2 *)                                                                                 *)
(* 		(* Return a pair of used and unused slices *)                                                                                         *)
(* 		  match l_l_slices with                                                                                                               *)
(* 			| [] -> ([], [])                                                                                                                    *)
(* 			| l_x::l_l_rest ->                                                                                                                  *)
(* 			  let (l_used_x, l_unused_x, marked_l_l_rest) =                                                                                     *)
(* 				List.fold_left (fun (a_l_x, a_l_ux, a_l_l_rest) (x_is_marked, (x_is_sat, x)) -> (* (_, x) is (x_is_sat, x) *)                     *)
(* 				  if x_is_marked then ((x_is_sat, x)::a_l_x, a_l_ux, a_l_l_rest) (* x shared variables with some previous lists of slices *)      *)
(* 				  else                                                                                                                            *)
(* 				    (* Mark all slice which overlaps with x *)                                                                                    *)
(* 					let n_l_l_rest = List.map (fun l_y ->                                                                                           *)
(* 					  List.fold_left (fun acc (y_is_marked, (y_is_sat, y)) ->                                                                       *)
(* 						if y_is_marked then (y_is_marked, (y_is_sat, y))::acc                                                                         *)
(* 						else (Gen.BList.overlap_eq eq_spec_var x.memo_group_fv y.memo_group_fv, (y_is_sat, y))::acc                                   *)
(* 					  ) [] l_y) a_l_l_rest in                                                                                                       *)
(* 					let n_l_x, n_l_ux =                                                                                                             *)
(* 					  if (List.exists (fun l_y ->                                                                                                   *)
(* 						List.exists (fun (_, (_, y)) ->                                                                                               *)
(* 						  Gen.BList.overlap_eq eq_spec_var x.memo_group_fv y.memo_group_fv) l_y)                                                      *)
(* 							a_l_l_rest) then                                                                                                            *)
(* 						((x_is_sat, x)::a_l_x, a_l_ux)                                                                                                *)
(* 					  else                                                                                                                          *)
(* 						(a_l_x, (x_is_sat, x)::a_l_ux)                                                                                                *)
(* 					in (n_l_x, n_l_ux, n_l_l_rest)                                                                                                  *)
(* 				) ([], [], l_l_rest) l_x                                                                                                          *)
(* 			  in                                                                                                                                *)
(* 			  let r_l_x, r_l_ux = filter_slices marked_l_l_rest in                                                                              *)
(* 			  (l_used_x::r_l_x, l_unused_x::r_l_ux)                                                                                             *)
(* 		in                                                                                                                                    *)
(* 		let (used_slices, unused_slices) = filter_slices (List.map (fun l_x -> List.map (fun x -> (false, x)) l_x) related_slices) in         *)
(* 		let ineq_related_slices = (List.concat used_slices) @ d_kb in                                                                         *)
(* 		let ineq_unrelated_slices = (List.concat unused_slices) @ unrelated_slices in                                                         *)

(* 	    (* Check SAT for each slice in ineq_related_slices before merging them to ineq *)                                                   *)

(* 		let (res, n_ineq_related_slices, l_formulas) = List.fold_left (fun (a_r, a_irs, a_l_f) (is_sat, x) ->                                 *)
(* 		  if not a_r then (a_r, a_irs, a_l_f) (* head of a_irs will be the UNSAT slice *)                                                     *)
(* 		  else                                                                                                                                *)
(* 			let f = MCP.fold_slice_gen x with_dupl with_inv true true in                                                                        *)
(* 			match is_sat with                                                                                                                   *)
(* 			  | None ->                                                                                                                         *)
(* 				let r = is_sat_sub_no f sat_subno in                                                                                              *)
(* 				(r, (Some r, x)::a_irs, f::a_l_f)                                                                                                 *)
(* 			  | Some r -> (r, (Some r, x)::a_irs, f::a_l_f)                                                                                     *)
(* 		) (true, [], []) ineq_related_slices in                                                                                               *)
(* 		if not res then (res, n_ineq_related_slices @ ineq_unrelated_slices)                                                                  *)
(* 		else                                                                                                                                  *)
(* 		  let f = join_conjunctions ((MCP.fold_slice_gen mg with_dupl with_inv true true)::l_formulas) in                                     *)
(* 		  let res = is_sat_sub_no f sat_subno in                                                                                              *)
(* 		  (res, n_ineq_related_slices @ ineq_unrelated_slices)                                                                                *)
(* 	else                                                                                                                                    *)
(* 	  let rec update_kb mg kb =                                                                                                             *)
(* 		match kb with                                                                                                                         *)
(* 		  | [] -> (true, [])                                                                                                                  *)
(* 		  | (is_sat, x)::rest ->                                                                                                              *)
(* 			if mg = x then                                                                                                                      *)
(* 			  match is_sat with                                                                                                                 *)
(* 				| None ->                                                                                                                         *)
(* 				  let f = MCP.fold_slice_gen mg with_dupl with_inv true true in                                                                   *)
(* 				  let r = is_sat_sub_no f sat_subno in (r, (Some r, x)::rest)                                                                     *)
(* 				| Some r -> (r, kb)                                                                                                               *)
(* 			else                                                                                                                                *)
(* 			  let (r, n_rest) = update_kb mg rest in                                                                                            *)
(* 			  (r, (is_sat, x)::n_rest)                                                                                                          *)
(* 	  in update_kb mg kb                                                                                                                    *)
(*   in                                                                                                                                      *)
(*   let kb = List.map (fun mg -> (None, mg)) mem in                                                                                         *)
(*   let (res, _) = List.fold_left (fun (a_r, a_kb) mg -> if not a_r then (a_r, a_kb) else is_sat_one_slice mg a_kb) (true, kb) mem in       *)
(*   res                                                                                                                                     *)

let is_sat_memo_sub_no (f : memo_pure) sat_subno with_dupl with_inv : bool =
  (* Modified version with UNSAT optimization *)
  (* if !do_slicing && !multi_provers then                       *)
  (*   is_sat_memo_sub_no_slicing f sat_subno with_dupl with_inv *)
  (* if !do_slicing && !opt_ineq then  *)
  if (not !dis_slc_ann) && !opt_ineq then
    is_sat_memo_sub_no_ineq_slicing f sat_subno with_dupl with_inv
    (* MCP.is_sat_memo_sub_no_ineq_slicing_complete f with_dupl with_inv (fun f -> is_sat_sub_no f sat_subno) *)
    (* MCP.is_sat_memo_sub_no_complete f with_dupl with_inv (fun f -> is_sat_sub_no f sat_subno) *)
    (* else if !do_slicing && !infer_lvar_slicing then *)
  else if (not !dis_slc_ann) && !infer_lvar_slicing then
    MCP.is_sat_memo_sub_no_complete f with_dupl with_inv (fun f -> is_sat_sub_no 5 f sat_subno)
  else is_sat_memo_sub_no_orig f sat_subno with_dupl with_inv

let is_sat_memo_sub_no (f : memo_pure) sat_subno with_dupl with_inv : bool =
  Debug.no_1 "is_sat_memo_sub_no" Cprinter.string_of_memo_pure_formula string_of_bool
    (fun f -> is_sat_memo_sub_no f sat_subno with_dupl with_inv) f	  

(* let is_sat_memo_sub_no_new (mem : memo_pure) sat_subno with_dupl with_inv : bool =                                          *)
(*   let memo_group_linking_vars_exps (mg : memoised_group) =                                                                  *)
(* 	let cons_lv = List.fold_left (fun acc mc -> acc @ (b_formula_linking_vars_exps mc.memo_formula)) [] mg.memo_group_cons in *)
(* 	let slice_lv = List.fold_left (fun acc f -> acc @ (formula_linking_vars_exps f)) [] mg.memo_group_slice in                *)
(* 	Gen.BList.remove_dups_eq eq_spec_var (cons_lv @ slice_lv)                                                                 *)
(*   in                                                                                                                        *)

(*   let fv_without_linking_vars_exps mg =                                                                                     *)
(* 	let fv_no_lv = Gen.BList.difference_eq eq_spec_var mg.memo_group_fv (memo_group_linking_vars_exps mg) in                  *)
(* 	(* If all fv are linking vars then mg should be a linking constraint *)                                                   *)
(* 	if (fv_no_lv = []) then mg.memo_group_fv else fv_no_lv                                                                    *)
(*   in                                                                                                                        *)

(*   let filter_fold_mg mg =                                                                                                   *)
(* 	let slice = mg.memo_group_slice in (* with_slice = true; with_disj = true *)                                              *)
(* 	let cons = List.filter (fun c -> match c.memo_status with                                                                 *)
(* 	  | Implied_R -> (*with_R*) with_dupl                                                                                     *)
(* 	  | Implied_N -> true                                                                                                     *)
(* 	  | Implied_P-> (*with_P*) with_inv) mg.memo_group_cons in                                                                *)
(* 	let cons  = List.map (fun c -> (BForm (c.memo_formula, None))) cons in                                                    *)
(* 	let asetf = List.map (fun (c1,c2) -> form_formula_eq_with_const c1 c2) (get_equiv_eq_with_const mg.memo_group_aset) in    *)
(* 	join_conjunctions (asetf @ slice @ cons)                                                                                  *)
(*   in                                                                                                                        *)

(*   let is_sat_slice_memo_pure (mp : memo_pure) : bool * (spec_var list * spec_var list * formula) list =                     *)
(* 	(* OUT: list of (list of fv, list of fv without linking vars, formula folded from SAT memo_groups) *)                     *)
(* 	let repart acc mg =                                                                                                       *)
(* 	  let (r, acc_fl) = acc in                                                                                                *)
(* 	  if not r then (r, [])                                                                                                   *)
(* 	  else                                                                                                                    *)
(* 		let f_mg = filter_fold_mg mg in                                                                                         *)
(* 		let r = is_sat_sub_no f_mg sat_subno in                                                                                 *)
(* 		if not r then (r, [])                                                                                                   *)
(* 		else                                                                                                                    *)
(* 		  let mg_fv_no_lv = fv_without_linking_vars_exps mg in                                                                  *)
(* 		  let (ol, nl) = List.partition (* overlap_list, non_overlap_list with mg *)                                            *)
(* 			(fun (_, vl, _) -> (Gen.BList.overlap_eq eq_spec_var vl mg_fv_no_lv)                                                  *)
(* 			) acc_fl                                                                                                              *)
(* 		  in                                                                                                                    *)
(* 		  let n_fvl = List.fold_left (fun a (fvl, _, _) -> a@fvl) mg.memo_group_fv ol in                                        *)
(* 		  let n_vl = List.fold_left (fun a (_, vl, _) -> a@vl) mg_fv_no_lv ol in                                                *)
(* 		  let n_fl = List.fold_left (fun a (_, _, fl) -> a@[fl]) [f_mg] ol in                                                   *)
(* 		  (r, (Gen.BList.remove_dups_eq eq_spec_var n_fvl,                                                                      *)
(* 			   Gen.BList.remove_dups_eq eq_spec_var n_vl,                                                                         *)
(* 			   join_conjunctions n_fl)::nl)                                                                                       *)
(* 	in List.fold_left repart (true, []) mp                                                                                    *)
(*   in                                                                                                                        *)

(*   let is_sat_slice_linking_vars_constraints (fl : (spec_var list * spec_var list * formula) list) : bool =                  *)
(* 	(* Separate the above list of formula list into two parts: *)                                                             *)
(* 	(* - Need to check SAT in combined form *)                                                                                *)
(* 	(* - Unneed to check SAT (constraints of linking vars) *)                                                                 *)
(* 	let rec repart (unchk_l, n_l, un_l) =                                                                                     *)
(* 	  (* If we know how to determine the constraints of linking vars,                                                         *)
   (* 		 we do not need n_l *)                                                                                                  *)
(* 	  match unchk_l with                                                                                                      *)
(* 		| [] -> true                                                                                                            *)
(* 		| (fvl, vl, f)::unchk_rest ->                                                                                           *)
(* 		  let f_lv = Gen.BList.difference_eq eq_spec_var fvl vl in                                                              *)
(* 		  if (f_lv = []) then                                                                                                   *)
(* 			let r = is_sat_sub_no f sat_subno in (* Can reduce the # of SAT checking here *)                                      *)
(* 			if not r then r                                                                                                       *)
(* 			else repart (unchk_rest, (fvl, vl, f)::n_l, un_l)                                                                     *)
(* 		  else                                                                                                                  *)
(* 			let is_related vl1 vl2 = Gen.BList.overlap_eq eq_spec_var vl1 vl2 in                                                  *)

(* 			(* Search relevant constraints in list of unchecked constraints *)                                                    *)
(* 			(* Move merged constraints into list of unneeded to check SAT constraints *)                                          *)
(* 			let (merged_fl1, unmerged_fl1) = List.partition (fun (_, vl1, _) -> is_related vl1 f_lv) unchk_rest in                *)

(* 			(* Search relevant constraints in list of needed to check SAT constraints *)                                          *)
(* 			(* Move merged constraints into list of unneeded to check SAT constraints *)                                          *)
(* 			let (merged_fl2, unmerged_fl2) = List.partition (fun (_, vl2, _) -> is_related vl2 f_lv) n_l in                       *)

(* 			(* Search relevant constraints in list of unneeded to check SAT constraints *)                                        *)
(* 			let merged_fl3 = List.find_all (fun (_, vl3, _) -> is_related vl3 f_lv) un_l in                                       *)

(* 			let n_f = join_conjunctions                                                                                           *)
(* 			  (List.fold_left (fun acc (_, _, f) -> acc@[f])                                                                      *)
(* 				 [f] (merged_fl1 @ merged_fl2 @ merged_fl3)) in                                                                     *)

(* 			let r = is_sat_sub_no n_f sat_subno in                                                                                *)
(* 			if not r then r                                                                                                       *)
(* 			else                                                                                                                  *)
(* 			  let n_unchk_l = unmerged_fl1 in                                                                                     *)
(* 			  let n_n_l = (fvl, vl, n_f)::unmerged_fl2 in                                                                         *)
(* 			  let n_un_l = merged_fl1 @ merged_fl2 @ un_l in                                                                      *)
(* 			  repart (n_unchk_l, n_n_l, n_un_l)                                                                                   *)
(* 	in                                                                                                                        *)
(* 	repart (fl, [], [])                                                                                                       *)
(*   in                                                                                                                        *)

(*   let (r, fl) = is_sat_slice_memo_pure mem in                                                                               *)
(*   let res =                                                                                                                 *)
(* 	if not r then r                                                                                                           *)
(* 	else is_sat_slice_linking_vars_constraints fl                                                                             *)
(*   in                                                                                                                        *)
(*   res                                                                                                                       *)

let is_sat_mix_sub_no (f : MCP.mix_formula) sat_subno with_dupl with_inv : bool = match f with
  | MCP.MemoF f -> is_sat_memo_sub_no f sat_subno with_dupl with_inv
  | MCP.OnePF f -> (if !do_sat_slice then is_sat_sub_no_with_slicing_orig else is_sat_sub_no 61) f sat_subno

let is_sat_mix_sub_no (f : MCP.mix_formula) sat_subno with_dupl with_inv =
  Debug.no_1 "is_sat_mix_sub_no"
    Cprinter.string_of_mix_formula
    string_of_bool
    (fun f -> is_sat_mix_sub_no f sat_subno with_dupl with_inv) f

let is_sat_msg_no_no prof_lbl (f:CP.formula) do_cache :bool = 
  let sat_subno = ref 0 in
  let () = Gen.Profiling.push_time prof_lbl in
  let sat = is_sat_sub_no_c 4 f sat_subno do_cache in
  let () = Gen.Profiling.pop_time prof_lbl in
  sat

(* let imply_one_xx k = imply_one k *)

let imply_sub_no ante0 conseq0 imp_no do_cache =
  let () = x_dinfo_zp (lazy ("IMP #" ^ imp_no ^ "\n")) no_pos in
  (* imp_no := !imp_no+1;*)
  let r = x_add imply_one 2 ante0 conseq0 imp_no do_cache in
  (* let () = print_endline "test" in *)
  r

let imply_sub_no ante0 conseq0 imp_no do_cache =
  (* let () = print_endline "inside imply_sub_no" in *)
  let pr = !CP.print_formula in
  Debug.no_2 "imply_sub_no" pr pr pr_none
    (fun _ _ -> imply_sub_no ante0 conseq0 imp_no do_cache) ante0 conseq0

let imply_msg_no_no ante0 conseq0 imp_no prof_lbl do_cache =
  let () = Gen.Profiling.push_time prof_lbl in  
  let r = x_add imply_sub_no ante0 conseq0 imp_no do_cache in
  let () = Gen.Profiling.pop_time prof_lbl in
  r

(* is below called by pruning *)
let imply_msg_no_no ante0 conseq0 imp_no prof_lbl do_cache process =
  Debug.no_2 "imply_msg_no_no " 
    Cprinter.string_of_pure_formula 
    Cprinter.string_of_pure_formula
    (fun (x,_,_)-> string_of_bool x) 
    (fun _ _ -> imply_msg_no_no ante0 conseq0 imp_no prof_lbl do_cache process) ante0 conseq0

let print_stats () =
  print_string ("\nTP statistics:\n");
  print_string ("omega_count = " ^ (string_of_int !omega_count) ^ "\n")

let prover_log = Buffer.create 5096

let get_prover_log () = Buffer.contents prover_log
let clear_prover_log () = Buffer.clear prover_log

let change_prover prover =
  clear_prover_log ();
  pure_tp := prover;
  start_prover ();;


let is_sat_raw (f: MCP.mix_formula) =
  is_sat_mix_sub_no f (ref 9) true true

let imply_raw ante conseq =
  let (res,_,_) = x_add mix_imply (MCP.mix_of_pure ante) (MCP.mix_of_pure conseq) "999" in
  res

let imply_raw ante conseq =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "imply_raw" pr pr string_of_bool imply_raw ante conseq

let imply_raw_mix ante conseq =
  let (res,_,_) = x_add mix_imply ante conseq "99" in
  res

let imply_raw_mix ante conseq =
  let pr = Cprinter.string_of_mix_formula in
  Debug.no_2 "imply_raw_mix" pr pr string_of_bool imply_raw_mix ante conseq

(* pre : xp1 --> xp0 *)
let check_diff xp0 xp1 =
  let (x,_,_) = x_add mix_imply xp0 xp1 "check_diff" in x

let check_diff xp0 xp1 =
  let pr1 = Cprinter.string_of_mix_formula in
  Debug.no_2 "check_diff" pr1 pr1 string_of_bool check_diff xp0 xp1

(* syn gist to remove conj in f1 already in f2 *)
let syn_gist f1 f2 =
  let x1 = split_conjunctions f1 in
  let x2 = split_conjunctions f2 in
  (* let x3 = List.filter (fun x -> not(List.exists (fun y -> equalFormula x y) x2)) x1 in *)
  let x3 = Gen.BList.difference_eq equalFormula x1 x2 in
  let x4 = Gen.BList.difference_eq equalFormula x2 x1 in
  is_empty x4, join_conjunctions x3

let norm_gist_result a b r = 
  let r = norm_pure_result r in
  (* To recover unexpected substition done by gist *)
  let xa = split_conjunctions a in
  let xr = split_conjunctions r in
  let xr = List.map (fun x ->
      if Gen.BList.mem_eq equalFormula x xa then x
      else
        try List.find (fun a -> imply_raw (mkAnd x b no_pos) a) xa
        with _ -> x
    ) xr in
  join_conjunctions xr

let om_gist f1 f2 =
  (* let is_done, f1 = syn_gist f1 f2 in *)
  (* if is_done then f1 *)
  (* else *)
    wrap_pre_post (fun (a, b) -> (norm_pure_input a, norm_pure_input b)) 
      (norm_gist_result f1 f2) (fun (f1, f2) -> Omega.gist f1 f2) (f1, f2)

let om_gist f1 f2 =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "om_gist" pr pr pr (fun _ _ -> om_gist f1 f2) f1 f2

let () = 
  CP.simplify := simplify;
  CP.oc_hull := oc_hull;
  Cast.imply_raw := imply_raw;
  (* CF.is_unsat_raw  := is_unsat_raw; *)
  CP.tp_imply := (fun l r -> Wrapper.wrap_dis_non_linear (imply_raw l) r);
  Excore.is_sat_raw := is_sat_raw;
  (* Excore.simplify_raw := simplify_raw; *) (* losing precision for ex25m5d.slk *)
  Excore.simplify_raw := (fun x -> if !Globals.old_tp_simplify then simplify_raw x else om_simplify x);
  Excore.pairwisecheck := pairwisecheck;
  Cformula.simplify_omega := (x_add_1 simplify_omega);
  Cfout.simplify_raw := simplify_raw;


(* type: CP.formula -> *)
(*   CP.formula -> *)
(*   string -> *)
(*   float -> (GlobProver.prover_process_t option * bool) option -> bool *)
