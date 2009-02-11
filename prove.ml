let debug = false
let trace s = if debug then (prerr_endline ("prove: "^s); flush stderr) else ()
let show_progress s = print_string s; flush stdout

let is_slave = ref false
let job_seq_no = ref 0

module Utils = struct
  let time_threshold = 3.
  let time_used func arg =
    let start_time = Unix.gettimeofday() in
    let res = func arg in     (* apply the function *)
    let time_str = (Unix.gettimeofday()) -. start_time in
    (res, time_str)
  
  let log_ch = ref stdout
  
  let open_log () =
    (* automatic create one log filename per day *)
    let t = Unix.localtime (Unix.time ()) in
    let filename = Printf.sprintf "%02d%02d%02d.log" t.Unix.tm_year t.Unix.tm_mon t.Unix.tm_mday in
    (* open the log file *)
    if Sys.file_exists filename = false then
      log_ch := open_out filename
    else
      log_ch := open_out_gen [Open_wronly; Open_append; Open_creat]	0o664 filename
  
  (* close log, should be called to actually save the log data. *)
  let close_log () = try close_out !log_ch with e -> ()
  
  (* write a string to the log *)
  let log_str s = output_string !log_ch s
  
  (* log information about proving task *)
  let log_info time prover_arg job_info =
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
  
  let kill_child parent_str =
    ()
end;;

(* when there are no slaves, use this function to serve the client         *)
(* directly                                                                *)
let do_dispatch prover formula =
  Tpdispatcher.set_tp prover;
  let result =
    match formula with
    | Tpdispatcher.Sat f -> Net.IO.to_string (Tpdispatcher.is_sat f)
    | Tpdispatcher.Simplify f -> Net.IO.to_string (Tpdispatcher.simplify f)
    | Tpdispatcher.Imply (f, g) -> Net.IO.to_string (Tpdispatcher.imply f g)
  in
  result

(* let slave_pipe_names = ref [||] let slave_pipes = ref [||] let          *)
(* num_slaves = ref 0                                                      *)

(* expand to list of provers [om] -> [omega;mona] *)
let expand prover_arg =
  if String.length prover_arg > 2 then
    (* if it is a shorthand for a combination of provers *)
    [prover_arg]
  else begin
    let get_prover_name c =
      if c = 'o' then "omega"
      else if c = 'm' then "mona"
      else if c = 'i' then "isabelle"
      else if c = 'c' then "cvcl"
      else "omega" (* TODO unknown..*)
    in
    let provers_list = ref [] in
    String.iter (fun c -> provers_list := !provers_list @ [get_prover_name c]) prover_arg;
    !provers_list
  end

(* Spawn itself in slave mode, connecting to the current process via fresh *)
(* pipes. Return the list of pipe names and IO channels                    *)
let spawn_slaves nslaves =
  (* parallel mode with num_slaves workers *)
  trace ("spawning slaves" ^ (string_of_int nslaves));
  (* create temporary channels *)
  let pipe_names = Array.make nslaves "" in
  for i = 0 to nslaves - 1 do
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
  let pipe_ios = Array.map Net.Pipe.init_client pipe_names in
  (Array.to_list pipe_names, Array.to_list pipe_ios)

(* Terminate other unused running provers. *)
let kill_others () =
  (* TODO kill the right ones *)
  let patterns = ["'oc input.oc'"; "'/usr/bin/mona -q'"] in
  let cmd = "pkill -9 -u" ^ (Unix.getenv("LOGNAME")) ^ " -f " in
  List.iter (fun s -> ignore(Sys.command (cmd ^ s))) patterns

(* When there are slaves, do send job to slaves this is used to run        *)
(* parallel proving with different solvers and return the first result,    *)
(* discard other tasks                                                     *)
let do_par_or channels prover_lst data =
  (* sending out tasks to do in parallel *)
  show_progress (" ");
  incr job_seq_no;
  let wait_fds =
    List.map2 (fun prover (ich, och) ->
            Net.IO.write_job och !job_seq_no prover data;
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
              if seqno = !job_seq_no && !result = "" then begin
                result := res;
(*                show_progress " got from: ";                          *)
(*                let i = ref (- 1) in                                  *)
(*                List.iter (fun c ->                                   *)
(*                        incr i;                                       *)
(*                        if c = fd then                                *)
(*                          show_progress (string_of_int !i) ) wait_fds;*)
                (* TODO kill other provers process *)                
              end) lst;
    end
  done;
  !result

(* main service function: wait for requests in the in_ch, do the task, and *)
(* write result to out_ch .                                                *)
let server_process in_ch out_ch =
  try
    Utils.open_log ();
    Utils.log_str "\n\n======= new session =======\n";
    if !is_slave then
      while true do
        show_progress "\npipe:wait job..";
        let (seq_no, prover_arg, formula) = Net.IO.read_job in_ch in
        show_progress " proving..";
        let result, time_used = Utils.time_used (do_dispatch prover_arg) formula in
        Net.IO.write_result out_ch seq_no result;
        
        Printf.printf " time used: %02.3f" time_used;
        Utils.log_info time_used prover_arg formula;
      done
    else begin
      let slave_pipe_names = ref [] and slave_channels = ref [] in
      try
        while true do
          show_progress "\nsock: wait job..";
          let (seq_no, prover_arg, formula) = Net.IO.read_job in_ch in
          let prover_list = expand prover_arg in
          
          if !slave_pipe_names = [] then begin (* spawn slaves if they are not created yet *)
            let n, c = spawn_slaves (List.length prover_list) in
            slave_pipe_names := n; slave_channels := c;
          end;
          
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
    "--socket", Arg.String (fun s -> port := s; use_pipe := false), " <port>: start prove server at socket 'port' on local host";
    "--dpipe", Arg.Unit (fun () -> named_pipe := ""; is_slave := true), " use default pipe";
    "--pipe", Arg.String (fun s -> named_pipe := s; is_slave := true), " <name>: use the named pipe";
    "--child", Arg.Set is_slave, "internal parameter, for child mode."
    ]
    (fun s -> ())
    ("Usage: " ^ Sys.argv.(0) ^ " --socket [port] |  | --pipe [name]");
  
  (* daemonize the process *)
  if Unix.fork() > 0 then begin
    print_endline "Server daemon started.";
    exit 0 (* spawn a child and parent exits *)
  end else begin
    ignore(Unix.setsid()); (* detach from terminal *)
    (* both slaves and manager need to start server to listen to jobs      *)
    (* while true do                                                       *)
    try
      if !use_pipe then begin
        print_string "Pipe server.";
        Net.Pipe.init_server !named_pipe server_process
      end else begin
        print_string "Socket server.";
        Net.Socket.init_server !port server_process;
      end
    with
    | End_of_file -> print_endline "END OF FILE"
    | Unix.Unix_error (err, _, _) ->
        print_endline (Unix.error_message err);
  end;

;;

main ()