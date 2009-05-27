(*|This module is code for both Workers/Slave or Manager/Master.                           *)
(*|Since they share common messages and utilities, relevant submodules are included:       *)
(*| - [Utils] contains some utility functions.                                             *)
(*| - [DBCache] stores formulas that has been proved, and can be retrieved later for speed.*)
(*| - [Log] writes some logging information about long running tasks.                      *)
(*| - [Worker] receives messages from Managers and calls to Tpdispatcher for proving,      *)
(*|      then returns the result to the Managers.                                          *)
(*| - [Managers] receives job from clients, creates Workers, and send out jobs to Workers. *)
(*|      When a Worker returns a good result, it returns the result to clients             *)
(*|      and tell Workers to cancel unneccessary tasks.                                    *)

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

module Utils = struct
  let sleep f = 
    let start = Unix.gettimeofday () in
    while (Unix.gettimeofday ()) -. start < f do
      let _ = Unix.select [] [] [Unix.stderr] f in ();
    done
  
  
  let time_used func arg =
    (** apply the [func] to [arg] and return the result with time it takes. *)
    let start_time = Unix.gettimeofday() in
    let res = func arg in     (* apply the function *)
    let time_str = (Unix.gettimeofday()) -. start_time in
    (res, time_str)
  
  let ignore_exn e = try ignore(e) with e -> trace "ignored exception" (Printexc.to_string e)
  let index_of elem lst =
    (** return the first index of [elem] in the list [lst] *)
    let rec find i elem lst =
      match lst with
      | [] -> - 1
      | hd:: tl -> if elem = hd then i else find (i + 1) elem tl
    in find 0 elem lst
  
  let expand prover =
    Str.split (Str.regexp ",") prover
  (* (* expand to list of provers [om] -> [omega;mona] *) let expand       *)
  (* prover_arg = if String.length prover_arg > 2 then (* if it is a       *)
  (* shorthand for a combination of provers *) [prover_arg] else begin let *)
  (* get_prover_name c = if c = 'o' then "omega" else if c = 'm' then      *)
  (* "mona" else if c = 'i' then "isabelle" else if c = 'c' then "cvcl"    *)
  (* else "omega" (* TODO unknown..*) in let provers_list = ref [] in      *)
  (* String.iter (fun c -> provers_list := !provers_list @                 *)
  (* [get_prover_name c]) prover_arg; !provers_list end                    *)
  
  let run_get_output cmd args =
    (** run the shell command [cmd] with the [args] and return the output as a list of strings *)
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
  
  let trim s =
    (* removes spaces from the beginning and end of a string *)
    let l = String.length s in
    let k1 = ref 0 in
    while !k1 < l & s.[!k1] = ' ' do incr k1 done;
    let k2 = ref (l - 1) in
    while !k2 >= 0 & s.[!k2] = ' ' do decr k2 done;
    if !k1 <= !k2 then
      String.sub s !k1 (!k2 - !k1 + 1)
    else
      ""
  
  let int_of_str s =
    (* return int value of string [s] which allows leading and trailing '  *)
    (* '                                                                   *)
    let s1 = trim s in
    (* Printf.printf "\n s1 = %s" s1; flush stdout; *)
    if s1 <> "" then int_of_string (s1) else 0
  
  let get_pids cmd_pattern_lst =
    (* this command print out string "PID" in the first line and pid of    *)
    (* process that its parent command line contains the [pattern]         *)
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
              if prover_lines <> [] then begin (* shoud be one <=1 *)
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

module Log = struct
  let log_ch = ref stdout
  let open_log () =
    (** open a daily log file for storing information long runing tasks *)
    (* automatic create one log filename per day *)
    let t = Unix.localtime (Unix.time ()) in
    let filename = Printf.sprintf "%02d%02d%02d.log" (t.Unix.tm_year + 1900) (t.Unix.tm_mon + 1) t.Unix.tm_mday in
    (* open the log file *)
    if Sys.file_exists filename then
      log_ch := open_out_gen [Open_wronly; Open_append]  0o664 filename
    else
      log_ch := open_out_gen [Open_wronly; Open_append; Open_creat]  0o664 filename
  
  let close_log () =
    (** [close log] should be called to actually save the log data. *)
    (*|    DBCache.close_db ();*)
    Utils.ignore_exn (close_out !log_ch)
  
  let log_str s =
    (** write a string to the log *)
    output_string !log_ch s; flush !log_ch
  
  let time_to_log = 3. (** threshold to log the formula to a file *)
  let log_info time prover job_info =
    try
    (* List.iter (fun job_info -> *)
    (** log information about proving task *)
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

module Worker = struct
  let is_calling_external_prover = ref false
  
  (* when there are no slaves, use this function to serve the client       *)
  (* directly                                                              *)
  let do_dispatch prover formula =
    let encode = Net.IO.to_string in
    (*|    if !use_cache && DBCache.is_cached (encode formula) then begin*)
    (*|      encode (true)                                               *)
    (*|    end else                                                      *)
    begin
      try
        Tpdispatcher.set_tp prover;
        match formula with
        | Tpdispatcher.Sat f -> encode (Tpdispatcher.is_sat f)
        | Tpdispatcher.Imply (f, g) -> encode (Tpdispatcher.imply f g)
        | Tpdispatcher.Simplify f -> encode (Tpdispatcher.simplify f)
      with e ->
          trace "do_dispatch" (Printexc.to_string e);
          encode (false) (* failed *)
    end
  
  let get_childchild_pid parent_pid =
    (* get youngest child of parent [ppid] *)
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
  
  let main_slave_loop in_ch out_ch =
    (* main slave's loop: wait for requests in the in_ch, do the task, and *)
    (* write result to out_ch .                                            *)
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

module Manager = struct
  exception Obsoleted_Seqno
  exception GroupDone of int (* raise when jobs in the group is done, the int value is the group/client_seqno *)
  
  type slave_info = int * in_channel * out_channel * string
  (* pid, input channel, output channel, pipename *)
  
  type client_job_info = int * int * float * string * Tpdispatcher.prove_type list * string
  (* client_seqno, index, timeout, prover, formulas, stopper *)
  
  type slave_job_info = int * int * float * string * Tpdispatcher.prove_type * string
  (* client_seqno, idx, timeout, prover, formulas * stopper *)
  
  let slaves_idle: slave_info list ref = ref []
  let slaves_busy: (slave_info * slave_job_info) list ref = ref []
  let jobs_queue: slave_job_info list ref = ref [] (* job queue for slaves *)
  
(*  let wait_slave_fds = ref []*)
  let remote_channels = ref []
  
  let connect_remote_slaves num locations =
    (* create [num] connections to servers at [locations], some location   *)
    (* may have none or more than one server                               *)
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
  
  (* Spawn itself in slave mode, connecting to the current process via     *)
  (* fresh pipes. Return the list of pipe names and IO channels            *)
  let spawn_slaves num_local_slaves =
    (* parallel mode with num_slaves workers create temporary channels *)
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
    (* create IO channels to communicates with the local slaves just       *)
    (* spawned                                                             *)
    let pipes = List.map Net.Pipe.init_client pipe_names in
    let pids = Utils.get_pids pipe_names in
    (pids, pipes, pipe_names)
  
  let cleanup () =
    try
    (* clean up child slaves *)
      List.iter (fun (id, ic, oc, fn) ->
              close_in ic; flush oc; close_out oc;
              Sys.remove (fn ^ ".i_pipe");
              Sys.remove (fn ^ ".o_pipe"))
        (!slaves_idle); (* @ !slaves_busy TODO *)
    with e -> trace "cleanup" (Printexc.to_string e)
  
  let create_slaves num_slaves =
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
  
  let send_jobs_to_slaves () =
    (* sending out formula to all provers to do in parallel *)
    while !slaves_idle <> [] && !jobs_queue <> [] do
      let slave:: slave_tl = !slaves_idle in
      let job:: job_tl = !jobs_queue in
      let (_, ich, och, _) = slave in
      let (seqno, idx, timeout, prover, formula, stopper) = job in
      Net.IO.write_job_to_slave och seqno idx timeout prover formula;
      
      slaves_busy := (slave, job) :: !slaves_busy;
      slaves_idle := slave_tl;
      jobs_queue := job_tl;
    done
  
  let cancel_jobs_of id =
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
  
  let get_busy_fds () =  
    List.map (fun ((pid, i, o, fn), job) -> Unix.descr_of_in_channel i) !slaves_busy
          
  let process_client_msg msg_type data =
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
  
  let process_slave_msg manager_out_ch client_seqno idx slave_result =
    (* return true if a result is sent to client, false otherwise *)
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
                  Net.IO.write_result manager_out_ch client_seqno id (Tpdispatcher.Result res);
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
  
  (* main manager function: wait for requests in the in_ch, do the task,   *)
  (* and write result to out_ch .                                          *)
  let main_manager_loop manager_in_ch manager_out_ch =
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
        let (in_fds, _, _) = Unix.select (manager_in_fd::busy_fds) [] [] (1.0) in
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
                      let _ = process_slave_msg manager_out_ch seqno idx result in ()
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

(* program's starting point *)
let main () =
  let use_pipe = ref true in
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
