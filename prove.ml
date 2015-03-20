#include "xdebug.cppo"
(**This module is code for both Workers/Slave or Manager/Master.                           *)
(**Since they share common messages and utilities, relevant submodules are included:       *)
(** - [Utils] contains some utility functions.                                             *)
(** - [DBCache] stores formulas that has been proved, and can be retrieved later for speed.*)
(** - [Log] writes some logging information about long running tasks.                      *)
(** - [Worker] receives messages from Managers and calls to Tpdispatcher for proving,      *)
(**      then returns the result to the Managers.                                          *)
(** - [Managers] receives job from clients, creates Workers, and send out jobs to Workers. *)
(**      When a Worker returns a good result, it returns the result to clients             *)
(**      and tell Workers to cancel unneccessary tasks.                                    *)

let debug = ref false and debuginfo = false
let trace f s = if !debug then (prerr_endline (f ^ ": "^s); flush stderr)
let show_info s = if debuginfo then (prerr_string s; flush stderr)

let is_slave = ref false  (* this flag set the program to work as a Worker or a Manager*)
let use_cache = ref true  (* turn off by command line to disable using cache *)
let cancel_job_signal = Sys.sigusr1  (* this signal is used to tell the Workers to stop what they are doing *)
let remote_locations = ref [] (* a list of hostname:port of managers *)
let is_cluster () = !remote_locations <> []
let user_name = Unix.getenv("LOGNAME")
let default_num_slaves = 2

(**[Utils] contains some utility functions.*)
module Utils = struct
  (** [sleep f] sleeps for [f] miliseconds *)
  let sleep (f:float) : unit = 
    let start = Unix.gettimeofday () in
    while (Unix.gettimeofday ()) -. start < f do
      (* let () = Unix.select [] [] [Unix.stderr] f in (); *)
      let () = Gen.Basic.restart  (Unix.select [] [] [Unix.stderr]) f in ();
    done  
  
  (** [time_used f a] applies the [f] to argument [a] and returns the result with duration it takes. *)
  let time_used (func: 'a -> 'b) (arg: 'a) : 'b * float =
    let start_time = Unix.gettimeofday() in
    let res = func arg in     (* apply the function *)
    let time_str = (Unix.gettimeofday()) -. start_time in
    (res, time_str)
  
  (** [ignore_exn e] evaluate [e] and prevent exceptions from being thrown out. *)
  let ignore_exn e = try ignore(e) with e -> trace "ignored exception" (Printexc.to_string e)
  
  (** [index_of elem lst] returns the first index of [elem] in the list [lst] *)
  let index_of elem lst =
    let rec find i elem lst =
      match lst with
      | [] -> - 1
      | hd:: tl -> if elem = hd then i else find (i + 1) elem tl
    in find 0 elem lst
  
  (** [expand s] expands a comma separated string [s] to the list of the elements in [s]. *)
  let expand (prover:string) : string list =
    Str.split (Str.regexp ",") prover
  
  (** [run_get_output cmd args] runs the shell command [cmd] with the arguments [args] and returns the output as a list of strings *)
  let run_get_output (cmd:string) (args : string array) : string list =
    let rd, wr = Unix.pipe () in
    let pid = Unix.create_process cmd args Unix.stdin wr Unix.stderr in
    Unix.close wr;
    let in_channel = Unix.in_channel_of_descr rd in
    let lines = ref [] in begin
      try
        while true do
          lines := input_line in_channel :: !lines
        done
      with End_of_file -> ()
    end;
    Unix.close rd;
    ignore_exn(Unix.waitpid [] pid);
    List.rev !lines
  
  (** [trim s] removes spaces from the beginning and end of a string *)
  let trim s =
    let l = String.length s in
    let k1 = ref 0 in
    while !k1 < l & s.[!k1] = ' ' do incr k1 done;
    let k2 = ref (l - 1) in
    while !k2 >= 0 & s.[!k2] = ' ' do decr k2 done;
    if !k1 <= !k2 then
      String.sub s !k1 (!k2 - !k1 + 1)
    else
      ""
  
  (** [int_of_str s] returns int value of string [s] that may contains leading/trailing spaces *)
  let int_of_str (s:string) : int =
    let s1 = trim s in
    (* Printf.printf "\n s1 = %s" s1; flush stdout; *)
    if s1 <> "" then int_of_string (s1) else 0
  
  (** [get_pids pat] gets pids of processes that its parent command line contains one of the element in [pat].         
    *)
  let get_pids (cmd_pattern_lst:string list) : int list =
    let get_pid s = int_of_str(String.sub s 0 5) in
    let output = run_get_output "ps" [|"ps"; "-opid,ppid,command"; "-u"^ user_name; "--no-header" |] in
    (* trace "output"; List.iter trace output; *)
    let prover_pids = ref [] in
    List.iter (fun pattern ->
            try
              let regexp = Str.regexp pattern in
              let prover_lines = List.filter (fun s ->
                        try Str.search_forward regexp s 0 >= 0
                        with Not_found -> false) output in
              assert (List.length prover_lines < 2);
              if prover_lines <> [] then begin (* shoud be <=1 *)
                let first_line = List.hd prover_lines in
                let prover_pid = get_pid first_line in
                prover_pids := prover_pid :: !prover_pids;
              end
            with Not_found -> ()
      ) cmd_pattern_lst;
    !prover_pids
  
end;;

(*|module DBCache = struct                                               *)
(*|  let log_db =                                                        *)
(*|    let filename = "cache.db" in                                      *)
(*|    (* open the log file *)                                           *)
(*|    if not (Sys.file_exists (filename ^ ".dir")) then begin           *)
(*|      Dbm.opendbm filename [Dbm.Dbm_rdwr; Dbm.Dbm_create] 0o666;      *)
(*|    end else begin                                                    *)
(*|      Dbm.opendbm filename [Dbm.Dbm_rdwr] 0o666;                      *)
(*|    end                                                               *)
(*|                                                                      *)
(*|  let close_db () = Dbm.close log_db                                  *)
(*|                                                                      *)
(*|  let is_cached job_info =                                            *)
(*|    try                                                               *)
(*|      let prover_arg = Dbm.find log_db job_info in                    *)
(*|      print_string "\ncache: already proved by ";                     *)
(*|      print_endline prover_arg;                                       *)
(*|      true                                                            *)
(*|    with Not_found -> false                                           *)
(*|                                                                      *)
(*|  let time_to_cache = 2. (** threshold to log the formula to a file *)*)
(*|  let add_to_cache time prover_arg job_info =                         *)
(*|    (** log information about proving task *)                         *)
(*|    if time >= time_to_cache then begin                               *)
(*|      let key = Net.IO.to_string job_info in                          *)
(*|      try                                                             *)
(*|        if not (is_cached key) then begin                             *)
(*|          Dbm.add log_db key prover_arg;                              *)
(*|          trace "Added to cache.";                                    *)
(*|        end                                                           *)
(*|      with e -> trace ("add_to_cache: " ^ (Printexc.to_string e));    *)
(*|    end                                                               *)
(*|end;;                                                                 *)

(**[Log] contains some logging functions.*)
module Log = struct
(**Log provides some logging utilities.*)

  let log_ch = ref stdout
  
  (** [open_log] opens a daily log file for storing information long runing tasks. It is called once at start up. *)
  let open_log () =
    (* automatic create one log filename per day *)
    let t = Unix.localtime (Unix.time ()) in
    let filename = Printf.sprintf "%02d%02d%02d.log" (t.Unix.tm_year + 1900) (t.Unix.tm_mon + 1) t.Unix.tm_mday in
    (* open the log file *)
    if Sys.file_exists filename then
      log_ch := open_out_gen [Open_wronly; Open_append]  0o664 filename
    else
      log_ch := open_out_gen [Open_wronly; Open_append; Open_creat]  0o664 filename
  
  (** [close_log] should be called to actually save the log data opened by [open_log]. *)
  let close_log () =
    (*|    DBCache.close_db ();*)
    Utils.ignore_exn (close_out !log_ch)
  
  (** [log_str s] writes string [s] to the log. *)
  let log_str s =
    output_string !log_ch s; flush !log_ch
  
  let time_to_log = 3. (** threshold to log the formula to a file *)

  (** [log_info time prover job] log information about the proving task. *)
  let log_info (time : float) (prover:string) (job_info: Tpdispatcher.prove_type) : unit =
    try
    (* List.iter (fun job_info -> *)
      if time >= time_to_log then begin
        let prove_type =
          match job_info with
          | Tpdispatcher.Sat f -> "Sat"
          | Tpdispatcher.Simplify f -> "Simplify"
          | Tpdispatcher.Imply (f, g) -> "Imply" in
        let s = Printf.sprintf "Time used: %2.3f, prover: %s type: %s" time prover prove_type in
        output_string !log_ch s;
        flush !log_ch;
        show_info (Printf.sprintf "logged %02.3fs." time)
      end
    (* formulas *)
    with e -> trace "log_info" (Printexc.to_string e)
end;;

(**[Worker] waits job requests to do the task, and returns results via channels. 
If it receives a cancel task request, it will kill the child if any.*)
module Worker = struct
  let is_calling_external_prover = ref false
  
  (** Call Tpdispatcher of HIP that starts external solvers to find solutions. 
  When there are no slaves, use this function to serve the client directly.
  @param prover string that specifies the prover to be used.
  @param formula the formula and type of prove to be solved.
  @return encoded string containing the result. 
  *)
  let do_dispatch (prover:string) (formula:Tpdispatcher.prove_type) : string =
	let encode = Net.IO.to_string in
    (*|    if !use_cache && DBCache.is_cached (encode formula) then begin*)
    (*|      encode (true)                                               *)
    (*|    end else                                                      *)
    begin
      try
        Tpdispatcher.set_tp prover;
        match formula with
        | Tpdispatcher.Sat f -> encode (x_add Tpdispatcher.is_sat f)
        | Tpdispatcher.Imply (f, g) -> encode (Tpdispatcher.imply f g)
        | Tpdispatcher.Simplify f -> encode (Tpdispatcher.simplify f)
      with e ->
          trace "do_dispatch" (Printexc.to_string e);
          encode (false) (* failed *)
    end
  
  (** [get_childchild_pid ppid] returns pid of the youngest child of the process with pid of [ppid].
    @param parent_pid pid of the parent.
    @return pid of the youngest child process. *)
  let get_childchild_pid (parent_pid:int) : int =
    let get_pid s = Utils.int_of_str(String.sub s 0 5) in
    let get_ppid s = Utils.int_of_str(String.sub s 6 5) in
    let ps_output = Array.of_list(Utils.run_get_output "ps" [|"ps"; "-opid,ppid"; "-u"^ user_name; "--no-header" |]) in
    
    let pids = Array.map get_pid ps_output in
    let ppids = Array.map get_ppid ps_output in
    let len = Array.length ppids in
    let i = ref 0 in
    while !i < len - 1 && ppids.(!i) <> parent_pid do incr i done; (* seek to the child line *)
    while !i < len && ppids.(!i + 1) = pids.(!i) do incr i done; (* loop through descendants to get the smallest *)
    if !i < len then pids.(!i) else - 1
  
  (** [main_slave_loop in_ch out_ch] waits for requests in the [in_ch], do the task specified in the request, and 
    write result to [out_ch].
    @param in_ch input channel. 
    @param out_ch output channel. 
    *)
  let main_slave_loop (in_ch : in_channel) (out_ch : out_channel) : unit =
    let kill_child_proceses _ =
      (* prover slave receives stop signal will trigger this function to   *)
      (* kill the running tp solvers                                       *)
      if !is_calling_external_prover then begin
        Utils.ignore_exn(
            let pid = get_childchild_pid (Unix.getpid ()) in
            if pid > 0 then begin
              Utils.ignore_exn (Unix.kill pid Sys.sigkill);
              (* Sys.command ("ps -f -p" ^ (string_of_int pid)); *)
              Utils.ignore_exn (Unix.waitpid [] pid)
            end
          )
      end;
    in
    try
    (* register this signal to cancel unneccessary jobs *)
      Sys.set_signal cancel_job_signal (Sys.Signal_handle kill_child_proceses);
      Log.open_log ();
      while true do
      (* show_info " s:wait job.."; *)
        try
          let msg_type, data = Net.IO.read in_ch in
          if msg_type = Net.IO.msg_type_job then begin
            is_calling_external_prover := true;
            let (client_seqno, idx, timeout, prover, formula) = data in
            try
            (* show_info " s:proving"; *)
              let result, time_used = Utils.time_used (do_dispatch prover) formula in
              (* show_info " s:proved"; *)
              Log.log_info time_used prover formula;
              Net.IO.write_result out_ch client_seqno idx (Some result);
              is_calling_external_prover := false;
            (* show_info " s:ret [Some]"; *)
            (*|              if !use_cache then Utils.ignore_exn(DBCache.add_to_cache time_used prover_arg formula);*)
            with
            | Unix.Unix_error (_, "kill", _) as e ->
                is_calling_external_prover := false; (* it is no longer needed, so no need to return anything. *)
                trace "main_slave_loop 0" (Printexc.to_string e);
            | e ->
                is_calling_external_prover := false;
                Net.IO.write_result out_ch client_seqno idx None; (* some error occurred, return failed result *)
                (* show_info " s:ret [None]"; *)
                trace "main_slave_loop 1" (Printexc.to_string e);
          end else begin
            is_calling_external_prover := false;
            failwith "main_slave_loop 2: Not implemented!";
          end;
          is_calling_external_prover := false;
        with
        | Net.IO.Read_error -> is_calling_external_prover := false
      done;
      (* show_info "\r \r"; *)
      Log.close_log ();
    with
    | End_of_file ->
        Log.close_log ();
        close_in in_ch;
        exit 0
    | e -> trace "main_slave_loop 3" (Printexc.to_string e);
        exit 0
end;;

(**[Manager] receives requests from clients (HIP), distributes the requests to workers and wait for the results. 
A request may be one task but want several solvers to try in parallel.
If a result came back and it sends the result to the client and cancel other tasks if they become redundant.*)
module Manager = struct
  exception Obsoleted_Seqno
  exception GroupDone of int (* raise when jobs in the group is done, the int value is the group/client_seqno *)
  
  (* pid, input channel, output channel, pipename *)
  type slave_info = int * in_channel * out_channel * string
  
  (* client_seqno, index, timeout, prover, formulas, stopper *)
  type client_job_info = int * int * float * string * Tpdispatcher.prove_type list * string
  
  (* client_seqno, idx, timeout, prover, formulas * stopper *)
  type slave_job_info = int * int * float * string * Tpdispatcher.prove_type * string
  
  let slaves_idle: slave_info list ref = ref []
  let slaves_busy: (slave_info * slave_job_info) list ref = ref []
  let jobs_queue: slave_job_info list ref = ref [] (** job queue for slaves *)
  
	(*  let wait_slave_fds = ref []*)
  let remote_channels :(in_channel * out_channel) list ref = ref [] (** channels of remote provers*)
  
  (** [connect_remote_slaves num locations] creates [num] connections to servers in [locations]. 
  Some location may have none or more than one connections. *)
  let connect_remote_slaves (num: int) (locations: string list) : (in_channel * out_channel) list =
    try
      if locations <> [] then begin
        let res = ref [] in
        while List.length !res < num do
          List.iter (fun loc ->
                  if List.length !res < num then
                    res := Net.Socket.init_client loc :: !res) locations
        done;
        !res
      end else []
    with e -> trace "connect_remote_slaves" "Cannot connect with cluster servers"; []
  
  (** [spawn_slaves num_local_slaves] spawns [num_local_slaves] processes and connects to these processes via fresh pipes. 
  @return a list of process ids, pipes, and pipe names. *)
  let spawn_slaves (num_local_slaves : int) : int list * (in_channel * out_channel) list * string list =
    (* create temporary channels *)
    let pipe_name_arr = Array.make num_local_slaves "" in
    for i = 0 to num_local_slaves - 1 do
      let temp_name = Filename.temp_file (user_name^".") ("." ^ (string_of_int (Unix.getpid ()))) in
      Array.set pipe_name_arr i temp_name;
      Unix.unlink temp_name;
    done;
    let pipe_names = Array.to_list pipe_name_arr in
    (* launch slave processes *)
    List.iter (fun name ->
            let cmd = Sys.executable_name ^ " --slave --pipe " ^ name in
            ignore(Unix.system cmd);
      ) pipe_names;
    (* create IO channels to communicates with the local slaves just spawned *)
    let pipes = List.map Net.Pipe.init_client pipe_names in
    let pids = Utils.get_pids pipe_names in
    (pids, pipes, pipe_names)
  
  (** clean up child slaves *)
  let cleanup () : unit =
    try
      List.iter (fun (id, ic, oc, fn) ->
              close_in ic; flush oc; close_out oc;
              Sys.remove (fn ^ ".i_pipe");
              Sys.remove (fn ^ ".o_pipe"))
        (!slaves_idle); (* @ !slaves_busy TODO *)
    with e -> trace "cleanup" (Printexc.to_string e)
  
  (** [create_slaves num_slaves] creates/connects to [num_slaves] slaves. 
  Depending on the configuration (parameters) some remote slaves are connected 
  and the remaining are created locally. 
  @param num_slaves number of slaves needed. *)
  let create_slaves (num_slaves: int) : unit =
    let num_remote_slaves = num_slaves / 2 in
    remote_channels := connect_remote_slaves num_remote_slaves !remote_locations;
    let num_remote_channels = (List.length !remote_channels) in
    
    let num_local_slaves = max (num_slaves - num_remote_channels) 0 in
    let pids, chs, pipes = spawn_slaves num_local_slaves in
    let temp = List.map2 (fun id (i, o) -> (id, i, o) ) pids chs in
    slaves_idle := List.map2 (fun (id, i, o) n -> (id, i, o, n)) temp pipes;
    
    at_exit cleanup;
    
    if num_remote_channels > 0 then  show_info (Printf.sprintf "Connected to %d remote server(s)." num_remote_channels);
    show_info (Printf.sprintf "Spawned %d slave(s)." (List.length pids))
  
  
  (** [send_jobs_to_slaves ] sends jobs in queue [jobs_queue] to all idle slaves to do in parallel *)
  let send_jobs_to_slaves () : unit =
    while !slaves_idle <> [] && !jobs_queue <> [] do
      let slave = List.hd !slaves_idle in
	  let slave_tl = List.tl !slaves_idle in
      let job = List.hd !jobs_queue in
	  let job_tl = List.tl !jobs_queue in
      let (_, ich, och, _) = slave in
      let (seqno, idx, timeout, prover, formula, stopper) = job in
      Net.IO.write_job_to_slave och seqno idx timeout prover formula;
      
      slaves_busy := (slave, job) :: !slaves_busy;
      slaves_idle := slave_tl;
      jobs_queue := job_tl;
    done
  
  (** [cancel_jobs_of id] cancels the executing job [id].
  @param id the id of the job.*)
  let cancel_jobs_of (id: int) : unit =
    slaves_busy :=
    List.flatten (List.map (fun (slave, job) ->
                let (pid, i, o, fn) = slave in
                let (seqno, idx, timeout, prover, formula, stopper) = job in
                if id = - 1 || seqno = id then begin
                  slaves_idle := slave :: !slaves_idle;
                  Utils.ignore_exn(Unix.kill pid cancel_job_signal;);
                  []
                end else [(slave, job)]
          ) !slaves_busy)
  
  (** [get_busy_fds ()] extracts the list of file descriptors of busy (working) slaves.*)
  let get_busy_fds () : Unix.file_descr list =  
    List.map (fun ((pid, i, o, fn), job) -> Unix.descr_of_in_channel i) !slaves_busy
          
  (** [process_client_msg msg_type data] process the message of type [msg_type] sent from a client. 
  @param msg_type type of message.
  @param data message content. *)
  let process_client_msg (msg_type: int) (data: int * float * string * Tpdispatcher.prove_type list * string ) : unit =
    if msg_type = Net.IO.msg_type_job_list then begin
      show_info "job";
      let (seq_no, timeout, prover, formulas, stopper) = data in
      let idx = ref (- 1) in
      let new_jobs = List.map
          (fun f -> incr idx;  (seq_no, !idx, timeout, prover, f, stopper))
          formulas in
      jobs_queue := List.append !jobs_queue new_jobs;
      
      show_info "send slaves";
      send_jobs_to_slaves ()
(*      wait_slave_fds := List.append !wait_slave_fds fds;*)
      
    end else if msg_type = Net.IO.msg_type_cancel_job then begin
      show_info "process_client_msg cancel jobs";
      cancel_jobs_of (- 1);
    end else
      failwith "Not implemented!!"
  

  (** process message sent from a slave (worker). 
  @param manager_out_ch output channel of the manager.
  @param client_seqno client sequence number of the message.
  @param idx message id.
  @param slave_result type of result sent from slave. 
  @return true if a result is sent to client, false otherwise. *)
  let process_slave_msg (manager_out_ch: out_channel) (client_seqno:int) (idx:int) (slave_result: string option) : bool =
    let result_sent_to_client = ref false in
(*    show_info (Printf.sprintf "\n - process_slave_msg idles = %d busy =%d" (List.length !slaves_idle) (List.length !slaves_busy) );*)
    slaves_busy := List.filter (fun (slv, job) ->
            let (seqno, id, timeout, prover, formula, stopper) = job in
            if seqno = client_seqno && id = idx then begin
              slaves_idle := slv::!slaves_idle;
              match slave_result with
                None -> false
              | Some res ->  (* if result is some thing return it, *)
                  result_sent_to_client := true;
                  
                  (* trick to sleep *)
                  show_info " m:sending..\n";
                  Net.IO.write_result manager_out_ch client_seqno id (Some (Tpdispatcher.Result res));
                  Utils.sleep 0.001;
                  show_info " m:sent\n";
                  (* check if should stop other tasks *)
                  (*|                  begin try                                                 *)
                  (*|                    if res = stopper then raise (GroupDone client_seqno);   *)
                  (*|                  with e -> trace "process_slave_msg" (Printexc.to_string e)*)
                  (*|                  end;                                                      *)
                  false
            end else
              true
      ) !slaves_busy;
    if (List.length !slaves_idle) + (List.length !slaves_busy) <> default_num_slaves then
      failwith (Printf.sprintf "process_slave_msg: #idles=%d #busy=%d" (List.length !slaves_idle) (List.length !slaves_busy));
    if !result_sent_to_client then true else raise Obsoleted_Seqno
  
  (** [main_manager_loop in_ch out_ch] starts a loop that waits for requests in the in_ch, do the task in the request,
  and write result to out_ch.
  @param manager_in_ch input channel of the manager (master).
  @param manager_out_ch output channel of the manager (master).*)
  let main_manager_loop (manager_in_ch: in_channel) (manager_out_ch: out_channel) : unit =
    let manager_in_fd = Unix.descr_of_in_channel manager_in_ch in
    let start_time = ref 0. in
    (* let wait_job_ids = ref [] in let is_waiting_slaves () =             *)
    (* (!wait_slave_fds <> []) in                                          *)
    
    create_slaves default_num_slaves;
    
    (* main processing loop *)
    try
      Log.open_log ();
      Log.log_str "\n\n--- new session ---\n";
      Log.close_log ();
      let progress_dots = ref 1 in
      while true do
        flush_all ();
        send_jobs_to_slaves ();
        let busy_fds = get_busy_fds () in
        show_info (" wait " ^ (string_of_int (List.length busy_fds))); incr progress_dots;
        let (in_fds, _, _) = Gen.Basic.restart  (Unix.select (manager_in_fd::busy_fds) [] []) (1.0) in
        if in_fds <> [] then begin
          List.iter (fun fd ->
                  if fd = manager_in_fd then begin
                    (* message from client/other managers *)
                    show_info " \nm:got msg";
                    let msg_type, job_info = Net.IO.read manager_in_ch in
                    start_time := Unix.gettimeofday ();
                    process_client_msg msg_type job_info;
                    progress_dots := 1;
                  end else begin
                    show_info " m:get result";
                    try
(*                      wait_slave_fds := List.filter (fun d -> d <> fd) !wait_slave_fds; (* remove from waiting slaves *)*)
                      let seqno, idx, result = Net.IO.read_result (Unix.in_channel_of_descr fd) in
                      let () = process_slave_msg manager_out_ch seqno idx result in ()
                    with
                      GroupDone seqno -> cancel_jobs_of seqno;
                    | Obsoleted_Seqno -> show_info "skipped, obsolete job_id.";
                    | End_of_file -> trace "main_manager_loop" "EOF";
                    | Net.IO.Read_error -> trace "main_manager_loop" "Read_error ignored.";
                  end
            )
            in_fds;
        end;
      done;
    with e ->
        cleanup ();   (* close channels to inform the slaves to exits *)
        if e <> End_of_file then
          trace "main_manager_loop" (Printexc.to_string e)
        else
          raise Exit
end;;


(** program's entry *)
let main () =
  let use_pipe = ref true in (*flag specifies if pipe or socket is used (set by command line option --pipe)*)
  let port = ref "" in 
  let named_pipe = ref "" in
  let cluster_arg = ref "" in
  Arg.parse [
    "--cluster", Arg.Set_string cluster_arg, "<host:port>: service location of the secondary server";
    "--socket", Arg.String (fun s -> port := s; use_pipe := false), "<port>: Start prove server at the socket on the local host";
    "--pipe", Arg.String (fun s -> named_pipe := s), "<name>: use the named pipe";
    "--slave", Arg.Set is_slave, "Internal parameter, for slave only mode.";
    "--nocache", Arg.Clear use_cache, "Do not use cache.";
    "--verbose", Arg.Set debug, "Print debug and progress information.";
    ]
    (fun s -> ())
    ("Usage: " ^ Sys.executable_name ^ " <options>.");
  
  if !cluster_arg <> "" then remote_locations := Str.split (Str.regexp ";") !cluster_arg;
  
  Net.debug := !debug;
  
  (* daemonize the process *)
  if Unix.fork() > 0 then
    exit 0
  else begin
    ignore(Unix.setsid()); (* detach from terminal *)
    try
    (* both slaves and manager need to start server to listen to jobs *)
      let process_func = if !is_slave then Worker.main_slave_loop else Manager.main_manager_loop in
      if !use_pipe then
        Net.Pipe.init_server !named_pipe process_func
      else
        Net.Socket.init_server !port process_func
    with
    | Exit -> show_info "Session Ended!"; exit 0
    | Unix.Unix_error (err, _, _) -> trace "main" (Unix.error_message err);
    | e -> trace "main" (Printexc.to_string e);
  end
;;

main ()
