#include "xdebug.cppo"
open VarGen
open Gen.Basic

external set_close_on_exec : Unix.file_descr -> unit = "unix_set_close_on_exec";;

let try_set_close_on_exec fd =
  try set_close_on_exec fd; true with Invalid_argument _ -> false
;;

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
;;

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
;;

let open_proc cmd args out_file:int  =
  match Unix.fork() with
  |  0 -> begin 
			let output = Unix.openfile out_file [Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
			Unix.dup2 output Unix.stdout; Unix.close output;
			try Unix.execvp cmd args with _ -> exit 127 end
  | id -> id
;;

(* provers common methods *)
module PrvComms = 
struct

  open Globals
  open GlobProver
  type proc = GlobProver.prover_process_t
  exception Timeout

  let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout)
  let set_timer tsecs =
    ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = tsecs })

  (*checks for timeout when calling the fnc function (fnc has one argument - arg). If fnc runs for more than tsec seconds, a Timeout exception will be raised. 
    Otherwise, this method returns the result given by fnc. *)

  let maybe_raise_timeout (fn: 'a -> 'b) (arg: 'a) (limit:float) : 'b =
    let old_handler = Sys.signal Sys.sigalrm sigalrm_handler in
    let reset_sigalrm () = Sys.set_signal Sys.sigalrm old_handler in
    let () = set_timer limit in
    let proof_no = get_proof_no_str () in
    try
      let () = if !Globals.enable_time_stats then Timelog.logtime # timer_start proof_no limit else () in
      let res = fn arg in
      let x = Unix.getitimer Unix.ITIMER_REAL in
      (* let nt = limit -. x.Unix.it_value in *)
      let nt = limit -. x.Unix.it_value in
      let () = if !Globals.enable_time_stats then Timelog.logtime # timer_stop proof_no nt else () in
      set_timer 0.0;
      reset_sigalrm ();
      res
    with e ->
        begin
          let () = Timelog.logtime # timer_timeout proof_no limit in
          (* Debug.info_pprint (Timelog.logtime # print_timer)  no_pos; *)
          (* Debug.info_pprint ("TIMEOUT"^(Printexc.to_string e)) no_pos; *)
          raise e
        end


  let maybe_raise_timeout_num i (fnc: 'a -> 'b) (arg: 'a) (tsec:float) : 'b =
    Debug.no_1_num i "maybe_raise_timeout" string_of_float pr_no (fun _ -> maybe_raise_timeout fnc arg tsec) tsec 

  (* same as maybe_raise_timoeut just that it treats the timeout exception with the with_timeout function *)
  let maybe_raise_and_catch_timeout (fnc: 'a -> 'b) (arg: 'a) (tsec: float) (with_timeout: unit -> 'b): 'b =
    try
        let res = maybe_raise_timeout fnc arg tsec in
        res
    with 
      | Timeout -> (
          print_endline_quiet (" Timeout after " ^ (string_of_float tsec) ^ " secs") ;
          (with_timeout ())
        )
      | exc -> (
          print_endline_quiet ("maybe_raise_and_catch_timeout : Unexpected exception : " ^ (Printexc.to_string exc));
          raise exc
        )

  let maybe_raise_and_catch_timeout_sleek (fnc: 'a -> 'b) (arg: 'a) (with_timeout: 'b): 'b =
    try 
      if !sleek_timeout_limit > 0. then
        let res = maybe_raise_timeout fnc arg !sleek_timeout_limit in
        res 
      else fnc arg
    with 
    | Timeout -> with_timeout
    | exc -> raise exc

  let maybe_raise_and_catch_timeout_bool (fnc: 'a -> bool) (arg: 'a) (tsec: float) (with_timeout: unit -> bool): bool =
    Debug.no_1 "maybe_raise_and_catch_timeout" string_of_float string_of_bool 
        (fun _ -> maybe_raise_and_catch_timeout fnc arg tsec with_timeout) tsec 

  let maybe_raise_and_catch_timeout_string_bool (fnc: string -> bool) (arg: string) (tsec: float) (with_timeout: unit -> bool): bool =
    Debug.no_2 "maybe_raise_and_catch_timeout"  string_of_float (fun s -> s) string_of_bool 
        (fun _ _ -> maybe_raise_and_catch_timeout fnc arg tsec with_timeout) tsec arg

  (* closes the pipes of the named process *)
  let close_pipes (process: proc) : unit =
    (try
         flush process.outchannel;
         Unix.close (Unix.descr_of_out_channel process.outchannel);
         Unix.close (Unix.descr_of_in_channel process.errchannel)
     with
       | e -> () );
    (try
         Unix.close (Unix.descr_of_in_channel process.inchannel)
     with
       | e -> () )

  let log_to_file flag file_descr str =
    if flag then
      output_string file_descr str

  (* Starts a specific prover (creating new process using pipes). Parameters have the following meaning:
   ** log_all_flag - flag which tells whether to log proofs
   ** log-all - descriptor of the file where the log is written
   ** prover - 3tuple: (name of the prover, command to start the prover, process arguments as an array of strings)
   ** set_process - method that assigns the newly created process to the process ref used in <prover_name>.ml 
   ** prelude - method which prepares the prover for interactive use (first commands sent, first lines printed, etc)*)
  let start (log_all_flag: bool) (log_file: out_channel) (prover: string * string * string array) set_process prelude= 
    let (prover_name, prover_proc, prover_arg_array) = prover in
    let () = log_to_file log_all_flag log_file ("["^prover_name^".ml]: >> Starting "^prover_name^"...\n") in
    try
      let inchn, outchn, errchn, npid = open_process_full prover_proc prover_arg_array in
      let process = {name = prover_name; pid = npid; inchannel = inchn; outchannel = outchn; errchannel = errchn} in
      set_process process;
      prelude ()
    with
      | e -> begin
          print_endline_quiet ("\n["^prover_name^".ml ]Unexpected exception while starting prover "^ prover_name);
          flush stdout; flush stderr;
          log_to_file log_all_flag log_file ("["^prover_name^".ml]: >> Error while starting "^prover_name ^ "\n");
          raise e
      end

  (* Kills the prover process. Parameters have the following meaning:
   ** process - record with details about the process that needs to be killed (pid, in/out/errchannel, name)
   ** invocations - number of calls to this prover
   ** killing_signal - signal that kills the process. For most of provers, 2 should be enough to kill the process
   ** ending_function - function containing some final disposition for the prover (many provers don't need this, so one can just send (fun ()->() ) ) *)
  let stop (log_all_flag: bool) (log_file: out_channel) (process:proc) (invocations: int) (killing_signal: int) ending_function =
    let () = ending_function () in
    let () = log_to_file log_all_flag log_file ("\n[" ^ process.name  ^ ".ml]: >> Stop " ^ process.name ^ " after ... " ^ (string_of_int invocations) ^ " invocations\n") in
    flush log_file;
    close_pipes process;
    let fn () =
      (* print_endline "start kill"; *)
      Unix.kill process.pid killing_signal;
      ignore (Unix.waitpid [] process.pid)
      (* ;print_endline "end kill" *)
    in
    try 
        (* Timelog.logtime_wrapper "kill" *) fn ()
    with
      | e -> 
          (ignore e;
           log_to_file log_all_flag log_file("\n[" ^ process.name  ^ ".ml]: >> Exception while closing process\n"); 
           flush log_file)

  (* Restarts the prover. Parameters have the following meaning:
   ** reason - reason for restarting the prover
   ** prover_name - string containing the name of teh prover taht si restarted
   ** start - start method to be invoked when starting this prover 
   ** stop - stop method to be invoked when stoping this prover *)
  let restart (log_all_flag: bool) (log_file: out_channel) (reason:string) (prover_name: string) start stop =
    log_to_file log_all_flag log_file ("[" ^ prover_name ^ ".ml]: >> Restarting " ^ prover_name ^ " because of: " ^ reason) ;
    stop ();
    start ()

end;;
