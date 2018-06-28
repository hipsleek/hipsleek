open SBGlobals

module DB = SBDebug
module ES = ExtString.String

let pid_invalid = -1000;

type process = {
  prc_name : string;
  prc_cmd : string;
  prc_args : string array;
  prc_pid : int;
  prc_in_channel : in_channel;
  prc_out_channel : out_channel;
  prc_err_channel : in_channel;
}

let mk_dummy_proc (name: string) (cmd: string) (args : string array) =
  { prc_name = name;
    prc_cmd = cmd;
    prc_args = args;
    prc_pid = pid_invalid;
    prc_in_channel = stdin;
    prc_out_channel = stdout;
    prc_err_channel = stdin; }

let open_process cmd args : (in_channel * out_channel * in_channel * int) =
  let (in_read, in_write) = Unix.pipe() in
  let (out_read, out_write) = Unix.pipe() in
  let (err_read, err_write) = Unix.pipe() in
  let inchan = Unix.in_channel_of_descr in_read in
  let outchan = Unix.out_channel_of_descr out_write in
  let errchan = Unix.in_channel_of_descr err_read in
  let pid = match Unix.fork() with
    | 0 ->
      (* DB.pprint "Child process"; *)
      Unix.dup2 out_read Unix.stdin; Unix.close out_read;
      Unix.dup2 in_write Unix.stdout; Unix.close in_write;
      Unix.dup2 err_write Unix.stderr; Unix.close err_write;
      (* if not cloexec then List.iter Unix.close toclose; *)
      (try Unix.execvp cmd args with _ -> exit 127)
    | id ->
      (* DB.pprint "Parent process"; *)
      id
  in
  (* DB.pprint "Join process"; *)
  Unix.close out_read;
  Unix.close in_write;
  Unix.close err_write;
  (inchan, outchan, errchan, pid)

let close_process proc : unit =
  try
    flush proc.prc_out_channel;
    Unix.close (Unix.descr_of_out_channel proc.prc_out_channel);
    Unix.close (Unix.descr_of_in_channel proc.prc_err_channel);
    Unix.kill proc.prc_pid 9;
  with
  | e ->
    try
      Unix.close (Unix.descr_of_in_channel proc.prc_in_channel);
      Unix.kill proc.prc_pid 9;
    with | e -> ()

let read_output proc : string =
  let rec read acc =
    try
      let line = String.trim (input_line proc.prc_in_channel) in
      read (acc @ [line])
    with | End_of_file -> acc in
  let res = String.concat "\n" (read []) in
  res

let send_input proc input =
  output_string proc.prc_out_channel input;
  flush proc.prc_out_channel

let start_process proc_name cmd args : process =
  try
    let inchn, outchn, errchn, npid = open_process cmd args in
    let process =
      {prc_name = proc_name;
       prc_cmd = cmd;
       prc_args = args;
       prc_pid = npid;
       prc_in_channel = inchn;
       prc_out_channel = outchn;
       prc_err_channel = errchn } in
    process
  with
  | e ->
    flush stdout; flush stderr;
    raise e

let stop_process proc =
  close_process proc

let restart_process proc : process =
  let _ = stop_process proc in
  let name, cmd, args = proc.prc_name, proc.prc_cmd, proc.prc_args in
  start_process name cmd args

let check_proc_alive proc =
  (* NOTE: using this function slow down performance *)
  let proc_name = "ps" in
  let cmd = "ps" in
  let pid = string_of_int proc.prc_pid in
  (* DB.hprint "PID: " pr_id pid; *)
  let args = [|"-p"; pid |] in
  let nproc = start_process proc_name cmd args in
  let output = read_output nproc in
  (* DB.hprint "PS OUTPUT: " pr_id output; *)
  let res = ES.exists output pid in
  (* let _ = DB.hprint "EXISTS RES: " pr_bool res in *)
  res
