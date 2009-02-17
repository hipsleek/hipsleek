let debug = true
let trace s = if debug then (prerr_endline ("prove: "^s); flush stderr) else ()
let show_progress s = print_string s; flush stdout

let is_slave = ref false
let job_seq_no = ref 0

(* Spawn itself in slave mode, connecting to the current process via fresh *)
(* pipes. Return the list of pipe names and IO channels                    *)
let cluster_locations = ref ""

let is_cluster () = !cluster_locations <> "" 

module Utils = struct 
  let time_threshold = 3. (** threshold to log the formula to a file *)
  
  let time_used func arg =
    (** apply the [func] to [arg] and return the result with time it takes. *)
    let start_time = Unix.gettimeofday() in
    let res = func arg in     (* apply the function *)
    let time_str = (Unix.gettimeofday()) -. start_time in
    (res, time_str)
   
  let log_ch = ref stdout
  
  let open_log () = 
    (** open a daily log file for storing information long runing tasks *)
    (* automatic create one log filename per day *)
    let t = Unix.localtime (Unix.time ()) in
    let filename = Printf.sprintf "%02d%02d%02d.log" t.Unix.tm_year t.Unix.tm_mon t.Unix.tm_mday in
    (* open the log file *)
    if Sys.file_exists filename = false then
      log_ch := open_out filename
    else
      log_ch := open_out_gen [Open_wronly; Open_append; Open_creat]	0o664 filename
  
  let close_log () =
    (** close log; Should be called to actually save the log data. *)
    try close_out !log_ch with e -> ()
  
  let log_str s =
    (** write a string to the log *) 
    output_string !log_ch s 
  
  let log_info time prover_arg job_info =
    (** log information about proving task *)
    if time >= time_threshold then begin
      let ch = !log_ch in
      let prove_type =
        match job_info with
        | Tpdispatcher.Sat f -> "Sat"
        | Tpdispatcher.Simplify f -> "Simplify"
        | Tpdispatcher.Imply (f, g) -> "Imply" in
      let s = Printf.sprintf "\nTime used: %2.3f, prover: %s type: %s" time prover_arg prove_type in
      output_string ch s;
      flush ch;
      print_string " logged."
    end
   
  let index_of elem lst =
    (* find first index of [elem] in the list [lst] *)
    let rec find i elem lst = 
      match lst with 
      | [] -> - 1
      | hd:: tl -> if elem = hd then i else find (i + 1) elem tl
    in find 0 elem lst

  let expand prover_arg =
    Str.split (Str.regexp ",") prover_arg
(*  (* expand to list of provers [om] -> [omega;mona] *)                                      *)
(*  let expand prover_arg =                                                                   *)
(*    if String.length prover_arg > 2 then                                                    *)
(*      (* if it is a shorthand for a combination of provers *)                               *)
(*      [prover_arg]                                                                          *)
(*    else begin                                                                              *)
(*      let get_prover_name c =                                                               *)
(*        if c = 'o' then "omega"                                                             *)
(*        else if c = 'm' then "mona"                                                         *)
(*        else if c = 'i' then "isabelle"                                                     *)
(*        else if c = 'c' then "cvcl"                                                         *)
(*        else "omega" (* TODO unknown..*)                                                    *)
(*      in                                                                                    *)
(*      let provers_list = ref [] in                                                          *)
(*      String.iter (fun c -> provers_list := !provers_list @ [get_prover_name c]) prover_arg;*)
(*      !provers_list                                                                         *)
(*    end                                                                                     *)
    
end;;

(* when there are no slaves, use this function to serve the client         *)
(* directly                                                                *)
let do_dispatch prover formula =
  Tpdispatcher.set_tp prover;
  let encode = Net.IO.to_string in
  let result =
    match formula with
    | Tpdispatcher.Sat f -> 
      (try encode (Tpdispatcher.is_sat f); 
      with _ -> encode false;)
    | Tpdispatcher.Imply (f, g) -> 
      (try encode (Tpdispatcher.imply f g)
      with e ->  encode false;)
    | Tpdispatcher.Simplify f -> 
      (try  encode (Tpdispatcher.simplify f)
      with e -> encode f;)
  in
  result

let is_good_result formula res =  
	match formula with
	| Tpdispatcher.Sat f -> res
	| Tpdispatcher.Imply (f, g) -> res 
	| Tpdispatcher.Simplify f -> Net.IO.to_string f <> Net.IO.to_string res

let connect_remote_slaves num_connections location =
  try
    let arr = Array.make num_connections location in
    let remote_pipes = List.map Net.Socket.init_client (Array.to_list arr) in
    remote_pipes
  with e -> trace "Cannot connect remote"; []

(* Spawn itself in slave mode, connecting to the current process via fresh *)
(* pipes. Return the list of pipe names and IO channels                    *)
let spawn_slaves nslaves =
  (* parallel mode with num_slaves workers *)
  trace ("spawning slaves" ^ (string_of_int nslaves));
  let num_remote_slaves = if is_cluster () then nslaves / 2 else 0 in
  let num_local_slaves = nslaves - num_remote_slaves in
  (* create temporary channels *)
  let pipe_names = Array.make num_local_slaves "" in
  for i = 0 to num_local_slaves - 1 do
    let temp_name = Filename.temp_file (Unix.getenv("LOGNAME")) ("." ^ (string_of_int (Unix.getpid ()))) in
    Array.set pipe_names i temp_name;
  done;
  (* launch slave processes *)
  Array.iter (fun name ->
      (* let cmd = "prove --pipe 1>prove.log 2>prove.log" in *)
          let cmd = Sys.argv.(0) ^ " --child --pipe " ^ name in
          ignore(Unix.open_process_in cmd) (* TODO close them.. *)
    ) pipe_names;
  (* create IO channels *) 
  let local_pipes = Array.map Net.Pipe.init_client pipe_names in
  
  let remote_pipes =
    if is_cluster () && num_remote_slaves > 0 then
      connect_remote_slaves num_remote_slaves !cluster_locations
    else [] in
  
  (Array.to_list pipe_names, (Array.to_list local_pipes) @ remote_pipes)

(* Terminate other unused running provers. *)
let kill_others () =
  (* TODO kill the right ones *)
  let patterns = ["'oc input.oc'"; "'/usr/bin/mona -q'"] in
  let cmd = "pkill -9 -u" ^ (Unix.getenv("LOGNAME")) ^ " -f " in
  List.iter (fun s -> ignore(Sys.command (cmd ^ s))) patterns

(* When there are slaves, do send job to slaves this is used to run        *)
(* parallel proving with different solvers and return the first result,    *)
(* discard other tasks                                                     *)
let do_par_or channels prover_lst formula =
  (* sending out tasks to do in parallel *)
  incr job_seq_no;
  
  let wait_fds =
    List.map2 (fun prover (ich, och) ->
            Net.IO.write_job och !job_seq_no prover formula;
            Unix.descr_of_in_channel ich)
      prover_lst channels in
  
  show_progress " wait result";
  let result = ref "" in
  while !result = "" do
    show_progress ".";
    let (lst, _, _) = Unix.select wait_fds [] [] 5.0 in
    if lst <> [] then begin
      List.iter (fun fd ->
              let seqno, res = Net.IO.read_result (Unix.in_channel_of_descr fd) in
              if seqno = !job_seq_no && !result = "" && is_good_result formula res then begin
                result := res;
                show_progress (" got from: " ^ (string_of_int (Utils.index_of fd wait_fds)));
                (* TODO kill other provers process *)
              end 
              else if seqno <> !job_seq_no then 
                show_progress (" discarded: " ^ (string_of_int (Utils.index_of fd wait_fds)));
              ) lst;
(*      kill_others ()*)
    end
  done;
  !result


(* main slave's loop: wait for requests in the in_ch, do the task, and     *)
(* write result to out_ch .                                                *)
let slave_processing_loop in_ch out_ch =
  try
    Utils.open_log ();
    Utils.log_str "\n\n======= new session =======\n";
    while true do
      show_progress "\npipe:wait job..";
      let (seq_no, prover_arg, formula) = Net.IO.read_job in_ch in
      show_progress " proving..";
      let result, time_used = Utils.time_used (do_dispatch prover_arg) formula in
      Net.IO.write_result out_ch seq_no result;
      Printf.printf " time used: %02.3f" time_used;
      Utils.log_info time_used prover_arg formula;
    done;
    Utils.close_log ();
  with
  | End_of_file ->
      print_string "EOF. Done!";
      Utils.close_log ();
      close_in in_ch;
      flush out_ch

(* main manager function: wait for requests in the in_ch, do the task, and *)
(* write result to out_ch .                                                *)
let server_processing_loop in_ch out_ch =
  try
    Utils.open_log ();
    Utils.log_str "\n\n======= new session =======\n";
    begin
      let slave_pipe_names = ref [] and slave_channels = ref [] in
      try
        while true do
          show_progress "\nsock: wait job..";
          let (seq_no, prover_arg, formula) = Net.IO.read_job in_ch in
          let prover_list = Utils.expand prover_arg in
          
          if !slave_channels = [] then begin (* spawn slaves if they are not created yet *)
            let num_parallel_jobs = List.length prover_list in
            let n, c = spawn_slaves num_parallel_jobs in
            slave_pipe_names := n; slave_channels := c;
          end;
          print_int (List.length !slave_channels);
          print_int (List.length prover_list);
          let result, time_used = Utils.time_used (do_par_or !slave_channels prover_list) formula in
          Net.IO.write_result out_ch seq_no result;
          Printf.printf " time used: %02.3f" time_used;
          Utils.log_info time_used prover_arg formula;
        done;
      with e ->
      (* clean up child slaves *)
          List.iter (fun x -> close_in (fst x)) !slave_channels; (* close unused channels *)
          List.iter (fun fn ->
                  ignore (Sys.command ("pkill -9 -f " ^ fn)); (* kill by the temp named pipe in its arguments *)
                  Unix.unlink fn;) !slave_pipe_names;  (* delete temp pipes *)
          raise e;
    end;
    Utils.close_log ();
  with
  | End_of_file ->
      print_string "EOF. Done!";
      Utils.close_log ();
      close_in in_ch;
      flush out_ch

(* program's starting point *)
let main () =
  let use_pipe = ref true in
  let port = ref "" in
  let named_pipe = ref "" in
  Arg.parse [
    "--socket", Arg.String (fun s -> port := s; use_pipe := false), "<port>: Start prove server at the socket on the local host";
    "--cluster", Arg.Set_string cluster_locations, "<host:port>: service location of the secondary server";
    "--dpipe", Arg.Unit (fun () -> named_pipe := ""; is_slave := true), "Use default pipe";
    "--pipe", Arg.String (fun s -> named_pipe := s; is_slave := true), "<name>: use the named pipe";
    "--child", Arg.Set is_slave, "Internal parameter, for child mode.";
    ]
    (fun s -> ())
    ("Usage: " ^ Sys.argv.(0) ^ " --socket [port] |  | --pipe [name]");
  
  (* daemonize the process *)
  if Unix.fork() > 0 then begin
    print_endline "Server daemon started.";
    exit 0 (* spawn a child and parent exits *)
  end else begin
    ignore(Unix.setsid()); (* detach from terminal *)
    
    try
    (* both slaves and manager need to start server to listen to jobs *)
      let process_func = if !is_slave then slave_processing_loop else server_processing_loop in
      if !use_pipe then begin
        print_string "Pipe server.";
        Net.Pipe.init_server !named_pipe process_func;
      end else begin
        print_string "Socket server.";
        Net.Socket.init_server !port process_func;
      end
    with
    | End_of_file -> print_endline "END OF FILE"
    | Unix.Unix_error (err, _, _) ->
        print_endline (Unix.error_message err);
  end;

;;

main ()