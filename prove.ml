let debug = false
let trace s = if debug then (prerr_endline ("prove: "^s); flush stderr) else ()
let show_progress s = print_string s; flush stdout
 

module Utils = struct
	let time_threshold = 3.
	let time_used func arg =
		(* apply the function *)
		let start_time = Unix.gettimeofday() in
		let res = func arg in
		let time_str = (Unix.gettimeofday()) -. start_time in
		(res, time_str)

  let log_ch = ref stdout
    
	let open_log () =
		let t = Unix.localtime (Unix.time ()) in
		let filename = Printf.sprintf "%02d%02d%02d.log" t.Unix.tm_year t.Unix.tm_mon t.Unix.tm_mday in
		log_ch := 
      if Sys.file_exists filename then
		  	open_out filename
		  else
			  open_out_gen [Open_wronly; Open_append; Open_creat]	0o664 filename
	
	let close_log () =
    try  
	    trace "Clean up";
	    close_out !log_ch
    with e -> () 
	
	let log_info time provers job_info =
    let ch = !log_ch in
		output_string ch "\n\ntime used: ";
		output_string ch (Printf.sprintf "time used: %2.3f"  time);
    output_string ch "\n provers: ";
		List.iter (output_string ch " "; output_string ch) provers;
		output_string ch "\n job: ";
		output_string ch (
			match job_info with
			| Tpdispatcher.Sat f -> "Sat"
			| Tpdispatcher.Simplify f -> "Simplify"
			| Tpdispatcher.Imply (f,g) -> "Imply");
		output_string ch "\n";
		flush ch
	;;


end

(* expand to list of provers [om] -> [omega; mona] [oi] -> [omega;         *)
(* isabelle] etc.                                                          *)
let expand provers =
	let prover = List.hd provers in
	if String.length prover > 2 then (* if it is a shorthand for a combination of provers *)
	provers
	else begin
		let to_prove_name c =
			if c = 'o' then "omega"
			else if c = 'm' then "mona"
			else if c = 'i' then "isabelle"
			else if c = 'c' then "cvcl"
			else "omega" (* TODO unknown..*)
		in
		let provers_list = ref [] in
		String.iter (fun c -> provers_list := !provers_list @ [to_prove_name c]) prover;
		!provers_list
	end

let rec do_seq provers formula =
	let prover = (List.hd provers) in
	Tpdispatcher.set_tp prover;
	let result =
		match formula with
		| Tpdispatcher.Sat f -> Net.to_string (Tpdispatcher.is_sat f)
		| Tpdispatcher.Simplify f -> Net.to_string (Tpdispatcher.simplify f)
		| Tpdispatcher.Imply (f, g) -> Net.to_string (Tpdispatcher.imply f g)
	in
	if result <> "" (* TODO *)
	|| List.tl provers = [] then
		result
	else begin
		trace "no result---------------";
		do_seq (List.tl provers) formula
	end
;;

let rec do_par provers job =
	let prover = (List.hd provers) in
	Tpdispatcher.set_tp prover;
	let result =
		match job with
		| Tpdispatcher.Sat f -> Net.to_string (Tpdispatcher.is_sat f)
		| Tpdispatcher.Simplify f -> Net.to_string (Tpdispatcher.simplify f)
		| Tpdispatcher.Imply (f, g) -> Net.to_string (Tpdispatcher.imply f g)
	in
	if result <> "" (* TODO *)
	|| List.tl provers = [] then
		result
	else begin
		trace "no result---------------";
		do_seq (List.tl provers) job
	end
;;

let process in_ch out_ch =
	while true do
		show_progress "\nwait job..";
		match Net.read in_ch with
		| Some data ->
				let (provers, formula) = data in
				let prover_list = expand provers in
				show_progress "proving..";
				let result, time_used = Utils.time_used (do_seq prover_list) formula in
				Net.write out_ch result;
				Printf.printf "time used: %2.3f"  time_used;
				if time_used >= Utils.time_threshold then
					(Utils.log_info time_used provers formula;
        show_progress " logged";)
		| None -> ()
	done
			

let main () =
	let use_pipe = ref true in
	let port = ref "" in
	let named_pipe = ref "" in
	Arg.parse [
		"--socket", Arg.String (fun s -> port := s; use_pipe := false), 
      " <port>: start prove server at socket 'port' on local host";
		"--pipe", Arg.String (fun s  -> named_pipe := s),
      " <name>: use external provers via pipe 'name'"
		]
		(fun s -> ())
		("Usage: " ^ Sys.argv.(0) ^ " -[socket [port_no] | pipe [name]]");
	
	Utils.open_log ();
  
	if !use_pipe then begin
    trace "Use pipe.";
		Net.Pipe.init_server !named_pipe process;
	end else begin 
		trace "Use socket";
		Net.Socket.init_server !port process;
	end;
  
  Utils.close_log ();
	trace "End.";
;;

main ()