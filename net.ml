#include "xdebug.cppo"
(* let debug = ref false *)
let trace f s = if !Debug.debug_print then (prerr_string (Printf.sprintf "\n%d: %s: %s" (Unix.getpid ()) f s); flush stderr) else ()
let showinfo = true
let show_info s = if showinfo then (prerr_string s; flush stderr)

(** This module contains functions to serialize and unserialize data *)
module IO = struct
  let msg_type_job_list = 1
  and msg_type_job = 2
  and msg_type_result = 3
  and msg_type_cancel_job = 4
  and msg_type_none = 5
  and msg_type_continue = 6
  and msg_type_stop = 7

  exception Read_error (** Unknown error when reading/writing data via channels *)


  (** [to_string data] marshals [data] to a string *)
  let to_string (data: 'a) : string = Marshal.to_string data []

  (** [from_string s] unmarshals data from string [s]*)
  let from_string (s: string) : 'a =
    try
      Marshal.from_string s 0
    with
    | e -> trace "from_string" "Unmashaled failed"; raise e

  (** [read ch] read data from channel. The data always starts with an int specifying the data length.
      	@param ch input channel
      	@return data
      	*)
  let read (ch: in_channel) : 'a =
    try
      (* the data format is: first 4 bytes is the data length, then data of the length *)
      let data_len = input_binary_int ch in
      (* trace "read" ("len="^(string_of_int data_len)); *)
      if data_len > 0 then begin
        let data_str = String.create data_len in
        let () = really_input ch data_str 0 data_len in

        from_string (Bytes.to_string data_str)
      end else begin
        failwith "IO.read: Bad input data to Net!"
      end
    with
    | End_of_file -> trace "read" "EOF"; raise End_of_file
    | e -> trace "read" (Printexc.to_string e); raise Read_error

  let read_job ch = read ch

  let read_job_web ch = read ch


  (** [read_result ch] reads data from channel [ch] and check if data is of type {!Net.IO.msg_type_result}.
      	 @return data. *)
  let read_result (ch: in_channel) : 'a =
    let msg_type, data = read ch in
    assert (msg_type = msg_type_result);
    data

  (** [write ch data] marshals [data] and writes it to channel [ch].
      	@param ch output channel to be written.
      	@param data data to be written to the channel [ch].
      	*)
  let write (ch: out_channel) (data: 'a) : unit =
    try
      let data_str = to_string data in
      let data_len = String.length data_str in
      (* trace "write" ("len="^(string_of_int data_len)); *)
      output_binary_int ch data_len;
      output ch (Bytes.of_string data_str) 0 data_len;
      flush ch;
    with e -> trace "write" (Printexc.to_string e); raise e

  (** [write_job_to_slave ch seqno idx timeout prover_arg formula] writes
      	a tuple of (seqno, idx, timeout, prover_arg, formula) to the channel [ch].
      	The type of message is {!Net.IO.msg_type_job}.
      	@param ch output channel to be written
      	@return none
      	*)
  let write_job_to_slave (ch:out_channel) (seqno: int) (idx: int) (timeout: float)
      (prover_arg: string) (*(formula: Tpdispatcher.prove_type)*) formula : unit =
    write ch (msg_type_job, (seqno, idx, timeout, prover_arg, formula))

  (** [write_job_to_master ch seqno idx timeout prover_arg formula ] writes a tuple of (seqno, idx, timeout, prover_arg, formula) to the channel [ch].
      	The type of message is {!Net.IO.msg_type_job_list}.
      	@param ch output channel to be written.
      	@return none.
      	*)
  let write_job_to_master (ch: out_channel) (seqno: int) (timeout: float)
      (prover_arg:string) (*(formula: Tpdispatcher.prove_type)*) formula stopper =
    write ch (msg_type_job_list, (seqno, timeout, prover_arg, formula, stopper))


  let write_job ch seqno prover_arg formula =
    write ch (seqno, prover_arg, formula)
  let write_job_web ch seqno prover_arg formula prio =
    write ch (seqno, prover_arg, formula, prio)

  (** [write_result ch seqno idx result] writes a tuple of (seqno, idx, result) to the channel [ch].
      	The type of message is {!Net.IO.msg_type_result}.
      	@param ch output channel to be written
      	@return none *)
  let write_result (ch: out_channel) (seqno: int) (idx: int) (result:'a option) : unit =
    write ch (msg_type_result, (seqno, idx, result))

end


(**[Pipe] module contains functions for setup server and communication between processes on the same machine via Unix pipes *)
module Pipe = struct
  let pipe_prove_in = ref "" (**named pipe for reading requests*)
  let pipe_prove_out = ref "" (**named pipe for sending back results*)
  let open_in = open_in_gen [Open_binary; Open_rdonly] 0o600
  let open_out = open_out_gen [Open_binary; Open_wronly; Open_trunc] 0o600

  (** [make_pipes ()] creates a pair of named pipes for two processes on the same machine to communicate.
      	Pipe names are set in {!Pipe.pipe_prove_in} and {!Pipe.pipe_prove_out}.*)
  let make_pipes () =
    let rec mkpipe p num_retries =
      try
        if not (Sys.file_exists p) then Unix.mkfifo p 0o666
      with e ->
        trace "Pipe.make_pipes" (Printexc.to_string e);
    in
    mkpipe !pipe_prove_in 10;
    mkpipe !pipe_prove_out 10

  (** [set_pipe named_pipe] sets pipe names for {!Pipe.make_pipes}. *)
  let set_pipe (named_pipe:string) : unit =
    let s = if named_pipe = "" then (Unix.getenv "HOME") ^ "/" else named_pipe in
    pipe_prove_in := s^".i_pipe";
    pipe_prove_out := s^".o_pipe"

  (** remove named pipes (special files) *)
  let clean () =
    try
      Unix.unlink !pipe_prove_in;
      Unix.unlink !pipe_prove_out;
    with _ -> ()

  (** [init_client named_pipe] returns a pair of input and output channels with the prefix [named_pipe].
      	@param named_pipe prefix string of pipe name
      	@return a pair of (input,output) channels*)
  let init_client named_pipe =
    set_pipe named_pipe;
    try
      let out_ch = open_out !pipe_prove_in in
      let in_ch = open_in !pipe_prove_out in
      (in_ch, out_ch)
    with
    | e ->
      trace "Pipe.init_client" (Printexc.to_string e);
      exit 0

  (** [init_server named_pipe processing_func] starts a service that runs [processing_func] which waits data from [named_pipe] input channel,
      	consume the data, and return result to output channel.
      	@param named_pipe communication path for the client to send request to server that executes [processing_func].
      	@return none
      	*)
  let init_server named_pipe processing_func =
    (* set_pipe named_pipe; *)
    at_exit clean;
    set_pipe named_pipe;
    make_pipes ();
    while true do
      set_pipe named_pipe;
      let in_ch = open_in !pipe_prove_in in
      let out_ch = open_out !pipe_prove_out in
      try
        processing_func in_ch out_ch;
      with
      | Exit ->
        close_out out_ch;
        close_in in_ch;
        clean ();
        exit 0
      | Unix.Unix_error(err, ctx1, ctx2) ->
        trace "Pipe.init_server" (Printf.sprintf "init_server: %s, %s, %s\n" (Unix.error_message err) ctx1 ctx2);
    done
end

(**[Socket] module contains functions for setup server and communication between processes via TCP/IP socket *)
module Socket = struct
  let default_port = 8888 (**default port for socket communication*)

  (**[get_address host] returns inet_addr of the [host]*)
  let get_address (host: string) : Unix.inet_addr = (Unix.gethostbyname(host)).Unix.h_addr_list.(0)

  (** [get_host_port s ] extracts string [s] of the form [host:port_number].
      	If port is not provided, default_port is used.
      	If both host and port are not provided, current host and default port are used.
      	@param s string of the form [host:port] or [host]
      	*)
  let get_host_port (s: string) : string * int =
    let l = Str.split_delim (Str.regexp ":") s in
    match l with
    | [host; port] -> (host, int_of_string port)
    | [host] -> (host, default_port)
    | [] -> (Unix.gethostname (), default_port)
    | _ -> failwith "Invalid host:port format."


  (** [open_connection sockaddr] connects to socket [sockaddr] and return a pair of input and output channels.
      	@param sockaddr socket address.
      	@return a pair of (input,output) channels. *)
  let open_connection (sockaddr: Unix.sockaddr) : in_channel * out_channel =
    let domain =
      match sockaddr with
      | Unix.ADDR_UNIX _ -> Unix.PF_UNIX
      | Unix.ADDR_INET(_, _) -> Unix.PF_INET in
    let sock = Unix.socket domain Unix.SOCK_STREAM 0 in
    (*Unix.setsockopt sock Unix.TCP_NODELAY true;*)
    Unix.connect sock sockaddr;
    (Unix.in_channel_of_descr sock, Unix.out_channel_of_descr sock)

  (** [init_client host_port] to be setup by client by opening socket address at [host_port].
      	@param host_port string of host name and TCP/IP port to connect to.
      	@return a pair of input and output channels *)
  let init_client host_port : in_channel * out_channel =
    let server, port = get_host_port host_port in
    try
      show_info ("\nConnect to server: " ^ server ^ ":" ^ (string_of_int port));
      let address = get_address server in
      let socket_address = Unix.ADDR_INET (address, port) in
      let res = open_connection socket_address in
      show_info "..connected.\n";
      res
    with
    | Unix.Unix_error(err, ctx1, ctx2) as exn ->
      trace "Socket.init_client" (Printf.sprintf "init_client: %s, %s, %s\n" (Unix.error_message err) ctx1 ctx2);
      raise exn

  (** [establish_server server_fun sockaddr ] spawns a server process that serve [server_fun] at socket [sockaddr].
      	The server_fun will listen to data from input [sockaddr], process the received data and return the result to socket.
      	@param server_fun function that read input [sockaddr], process, and write to [sockaddr]. *)
  let establish_server (server_fun: (in_channel -> out_channel -> 'a)) (sockaddr: Unix.sockaddr) : unit =
    let domain =
      match sockaddr with
      | Unix.ADDR_UNIX _ -> Unix.PF_UNIX
      | Unix.ADDR_INET(_, _) -> Unix.PF_INET in
    let sock = Unix.socket domain Unix.SOCK_STREAM 0 in
    (*Unix.setsockopt sock Unix.TCP_NODELAY true;*)
    (* Unix.setsockopt_int sock Unix.SO_SNDBUF 50000; Unix.setsockopt_int  *)
    (* sock Unix.SO_RCVBUF 50000; Unix.setsockopt sock Unix.SO_DONTROUTE   *)
    (* true;                                                               *)

    Unix.bind sock sockaddr;
    Unix.listen sock 3;
    while true do
      let (s, caller) = Unix.accept sock in
      (* The "double fork" trick, the process which calls server_fun will  *)
      (* not leave a zombie process                                        *)
      match Unix.fork() with
        0 -> if Unix.fork() <> 0 then exit 0; (* The son exits, the grandson works *)
        let inchan = Unix.in_channel_of_descr s in
        let outchan = Unix.out_channel_of_descr s in
        server_fun inchan outchan;
        close_in inchan;
        close_out outchan
      | id -> Unix.close s; ignore(Unix.waitpid [] id) (* Reclaim the son *); ()
    done

  let init_client_fd (host_port: string): Unix.file_descr = (* connects to the host and returns a socket file descriptor*)
    let server, port = get_host_port host_port in
    try
      print_string ("Connect to server: " ^ server ^ ":" ^ (string_of_int port));
      let address = get_address server in
      let socket_address = Unix.ADDR_INET (address, port) in
      let sockfd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      let () = Unix.connect sockfd socket_address in
      print_string "..connected.\n";
      sockfd
    with Unix.Unix_error(err, ctx1, ctx2) as exn ->
      Printf.printf "Unix error: %s, %s, %s\n" (Unix.error_message err) ctx1 ctx2;
      raise exn

  (** [init_server port_str processing_func] start the server at port [port_str].
      	@param port_str string of port number. If empty, default_port is used.
      	@return none. *)
  let init_server (port_str: string) (processing_func: (in_channel -> out_channel -> 'a)) : unit =
    let port = if port_str = "" then default_port else int_of_string port_str in
    try
      let localhost = Unix.gethostname () in
      let address = get_address localhost in
      let socket_address = Unix.ADDR_INET (address, port) in
      show_info ("\nServer started at: " ^ localhost ^ ":" ^ (string_of_int port) ^ "\n\n");
      establish_server processing_func socket_address
    with
    | Unix.Unix_error(err, ctx1, ctx2) as exn ->
      trace "Socket.init_server" (Printf.sprintf "init_client: %s, %s, %s\n" (Unix.error_message err) ctx1 ctx2);
      raise exn

  (** [shutdown in_ch] shutdowns connection [in_ch] and ignores shutdown exception. *)
  let shutdown (in_ch: in_channel) : unit =
    try
      Unix.shutdown_connection in_ch
    with Unix.Unix_error(_, "shutdown", "") -> ()
end

