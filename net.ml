let debug = ref false
let trace f s = if !debug then (prerr_string (Printf.sprintf "\n%d: %s: %s" (Unix.getpid ()) f s); flush stderr) else ()
let showinfo = true
let show_info s = if showinfo then (prerr_string s; flush stderr)

(* marshalling data and format of in/out data. *)
module IO = struct
	let msg_type_job_list = 1
	and msg_type_job = 2
	and msg_type_result = 3
	and msg_type_cancel_job = 4
	and msg_type_none = 5
	and msg_type_continue = 6
	and msg_type_stop = 7
	
	exception Read_error
	
	let to_string data = Marshal.to_string data []
	
	let from_string s =
		try
			Marshal.from_string s 0
		with
		| e -> trace "from_string" "Unmashaled failed"; raise e
	
	(* read data from channel, the format is: (4 bytes data length | data) *)
	let read ch =
		try
			let data_len = input_binary_int ch in
			(* trace "read" ("len="^(string_of_int data_len)); *)
			if data_len > 0 then begin
				let data_str = String.create data_len in
				let _ = really_input ch data_str 0 data_len in
				
				from_string data_str
			end else begin
				failwith "IO.read: Bad input data to Net!"
			end
		with
		| End_of_file -> trace "read" "EOF"; raise End_of_file
		| e -> trace "read" (Printexc.to_string e); raise Read_error
	
	let read_result ch =
		let msg_type, data = read ch in
		assert (msg_type = msg_type_result);
		data
	
	let write ch data =
		try
			let data_str = to_string data in
			let data_len = String.length data_str in
			(* trace "write" ("len="^(string_of_int data_len)); *)
			output_binary_int ch data_len;
			output ch data_str 0 data_len;
			flush ch;
		with e -> trace "write" (Printexc.to_string e); raise e
	
	let write_job_to_slave ch seqno idx timeout prover_arg formula =
		write ch (msg_type_job, (seqno, idx, timeout, prover_arg, formula))
	
	let write_job_to_master ch seqno timeout prover_arg formula stopper =
		write ch (msg_type_job_list, (seqno, timeout, prover_arg, formula, stopper))
	
	let write_result ch seqno idx result =
		write ch (msg_type_result, (seqno, idx, result))
	
end

module Pipe = struct
	let pipe_prove_in = ref ""
	let pipe_prove_out = ref ""
	let open_in = open_in_gen [Open_binary; Open_rdonly] 0o600
	let open_out = open_out_gen [Open_binary; Open_wronly; Open_trunc] 0o600
	
	let make_pipes () =
		let rec mkpipe p num_retries =
			try
				if not (Sys.file_exists p) then Unix.mkfifo p 0o666
			with e ->
					trace "Pipe.make_pipes" (Printexc.to_string e);
		in
		mkpipe !pipe_prove_in 10;
		mkpipe !pipe_prove_out 10
	
	let set_pipe named_pipe =
		let s = if named_pipe = "" then (Unix.getenv "HOME") ^ "/" else named_pipe in
		pipe_prove_in := s^".i_pipe";
		pipe_prove_out := s^".o_pipe"
	
	let clean () =
		try
			Unix.unlink !pipe_prove_in;
			Unix.unlink !pipe_prove_out; 
		with _ -> ()
	
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
	
	let init_server	named_pipe processing_func =
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
	
	let open_connection sockaddr =
		let domain =
			match sockaddr with
			| Unix.ADDR_UNIX _ -> Unix.PF_UNIX
			| Unix.ADDR_INET(_, _) -> Unix.PF_INET in
		let sock = Unix.socket domain Unix.SOCK_STREAM 0 in
		(*Unix.setsockopt sock Unix.TCP_NODELAY true;*)
		Unix.connect sock sockaddr;
		(Unix.in_channel_of_descr sock, Unix.out_channel_of_descr sock)
	
	let init_client host_port =
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
	
	let establish_server server_fun sockaddr =
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
	
	let init_server port_str processing_func =
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
	
	let shutdown in_ch =
		try
			Unix.shutdown_connection in_ch
		with Unix.Unix_error(_, "shutdown", "") -> ()
end

