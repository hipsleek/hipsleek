let debug = true
let trace s = if debug then (prerr_endline ((string_of_int (Unix.getpid ()))^" - "^s); flush stderr) else ()

(* marshalling data and format of in/out data. *)
module IO = struct
  let to_string data = Marshal.to_string data []
  
  let from_string s =
    try
      Marshal.from_string s 0
    with e -> trace "Unmashaled failed"; raise e
  
  let input_len ch str len =
    try
      really_input ch str 0 len
    with End_of_file -> trace "End of file!"
    | e -> trace "Unmashaled failed";
        trace (string_of_int len); raise e
  
  (* read data from channel, the format is: (4 bytes data length | data) *)
  let read ch =
    let data_len = input_binary_int ch in
    (* trace ("read data len="^(string_of_int data_len)); *)
    if data_len > 0 then begin
      let data_str = String.create data_len in
      let _ = input_len ch data_str data_len in
      from_string data_str
    end else begin
      failwith "Bad input data to Net!"
    end
  
  let read_job ch = read ch
  
  let read_result ch = read ch
  
  let write ch data =
    let data_str = to_string data in
    let data_len = String.length data_str in
    (* trace ("write data len="^(string_of_int data_len)); *)
    output_binary_int ch data_len;
    output ch data_str 0 data_len;
    flush ch
  
  let write_job ch seqno prover_arg formula =
    write ch (seqno, prover_arg, formula)
  
  let write_result ch seqno result =
    write ch (seqno, result)
end

module Pipe = struct
  let pipe_prove_in = ref ""
  let pipe_prove_out = ref ""
  let open_in = open_in_gen [Open_binary; Open_rdonly] 0o600
  let open_out = open_out_gen [Open_wronly; Open_append; Open_creat] 0o600
  
  let set_pipe named_pipe =
    let s = if named_pipe = "" then (Unix.getenv "HOME") ^ "/" else named_pipe in
    pipe_prove_in := s^".i_pipe";
    pipe_prove_out := s^".o_pipe";
    let mkpipe p = if Sys.file_exists p = false then
        try Unix.mkfifo p 0o666 with
          e -> print_string "\n\nFATAL: Cannot make pipe!!!!!!!!!!!!!!!!!\n"; exit 0;
    in
    mkpipe !pipe_prove_in;
    mkpipe !pipe_prove_out;
    ()
  
  let init_client named_pipe =
    set_pipe named_pipe;
    try
      let out_ch = open_out !pipe_prove_in in
      let in_ch = open_in !pipe_prove_out in
      (in_ch, out_ch)
    with Unix.Unix_error(err, ctx1, ctx2) as exn ->
        Printf.printf "Unix error: %s, %s, %s\n" (Unix.error_message err) ctx1 ctx2;
        raise exn
  
  let init_server	named_pipe call_back =
    set_pipe named_pipe;
    print_endline ("Prover service started at pipes: " ^ (if named_pipe <> "" then named_pipe else "<default>"));
    
    while true do
      try
        let in_ch = open_in !pipe_prove_in in
        let out_ch = open_out !pipe_prove_out in
        call_back in_ch out_ch
      with End_of_file -> trace "Section ended!"
    done
  
  let shutdown in_ch =
    try close_in in_ch;	with _ -> ()
  
end

module Socket = struct
  let default_port = 8888
  let get_address host = (Unix.gethostbyname(host)).Unix.h_addr_list.(0)
  
  let get_host_port s =
    let l = Str.split_delim (Str.regexp ":") s in
    match l with
    | [host; port] -> (host, int_of_string port)
    | [host] -> (host, default_port)
    | [] -> (Unix.gethostname (), default_port)
    | _ -> failwith "Invalid host:port format."
  
  let init_client host_port =
    let server, port = get_host_port host_port in
    try
      print_string ("Connect to server: " ^ server ^ ":" ^ (string_of_int port));
      let address = get_address server in
      let socket_address = Unix.ADDR_INET (address, port) in
      let res = Unix.open_connection socket_address in
      print_string "..connected.\n";
      res
    with Unix.Unix_error(err, ctx1, ctx2) as exn ->
        Printf.printf "Unix error: %s, %s, %s\n" (Unix.error_message err) ctx1 ctx2;
        raise exn
  
  let init_server port_str callback =
    let port = if port_str = "" then default_port else int_of_string port_str in
    try
      let localhost = Unix.gethostname () in
      let address = get_address localhost in
      let socket_address = Unix.ADDR_INET (address, port) in
      print_string ("\nStart server at: " ^ localhost ^ ":" ^ (string_of_int port));
      Unix.establish_server callback socket_address
    with Unix.Unix_error(err, ctx1, ctx2) as exn ->
        Printf.printf "Unix error: %s, %s, %s\n" (Unix.error_message err) ctx1 ctx2;
        raise exn
  
  let shutdown in_ch =
    try
      Unix.shutdown_connection in_ch
    with Unix.Unix_error(_, "shutdown", "") -> ()
end

