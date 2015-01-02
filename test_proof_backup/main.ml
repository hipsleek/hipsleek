(*z3-steps-test1-no-slicing-script.smt2*)
external set_close_on_exec : Unix.file_descr -> unit = "unix_set_close_on_exec";;

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let set_source_file arg = 
  Globals.source_file := arg 

let process_cmd_line () = Arg.parse Scriptarguments.run_arguments set_source_file usage_msg

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

let rec icollect_output chn accumulated_output : string list =
	let output = try
					 let line = input_line chn in
                     (*let _ = print_endline ("locle2" ^ line) in*)
                     if ((String.length line) > 7) then (*something diff to sat/unsat/unknown, retry-may lead to timeout here*)
					 icollect_output chn (accumulated_output @ [line])
                    else accumulated_output @ [line]
				with
					| End_of_file -> accumulated_output in
		output
		
let read_file_2 filename = 
  (*let _= print_endline ("file:"^ !Globals.source_file) in*)
  let lines = ref "" in
	let set_options = ref "" in
  let list_check = ref ([]:(string) list) in
  let chan = open_in filename in
  try
      while true; do
        let b = input_line chan in
					(* let _=print_endline (b) in *)
					(* try                                   *)
					(* 	 let _= BatString.find b "(set-" in *)
					(* 	 set_options := !set_options^b^"\n" *)
					(* with _->	                            *)
					 let _=lines := !lines^b^"\n" in	
           try 
             let ic= BatString.find b "(check-sat)" in
				     try
						   let ise= BatString.find b ";" in	
				       if (ic < ise) then
								begin 
								  list_check := !list_check @ [!lines];
									lines := ""
								end    	     
				     with _ -> let _=list_check := !list_check @ [!lines] in lines := ""    	    
					  with _->()
					
      done; 
      close_in chan;
			("",[],"")
  with End_of_file ->
		begin	
      close_in chan;
			(* let _= List.map (fun x-> print_endline (x)) !list_check in *)
      (!set_options,!list_check,!lines) (*return the set-options, body and the last*)
	  end		
;;

let incr_nums_check_sat ()=
	  Globals.nums_of_check_sat := !Globals.nums_of_check_sat + 1 	 

let read_file filename =
  let chan = open_in filename in
  let lip= Std.input_list chan in
  let _= close_in in
  (*let _= print_endline ("file2:"^ !Globals.source_file) in *)
  List.fold_left ( fun a b-> 
		let _=
      try 
         let ic= BatString.find b "(check-sat)" in
				 try
						 let ise= BatString.find b ";" in	
				     if (ic < ise) then incr_nums_check_sat ()     	     
				 with _ -> incr_nums_check_sat ()
      with _-> ()
		in a^"\n"^b	 
     ) "" lip 
;;

let start ()= 
    try
        open_process_full "z3" [|"z3";"-smt2";"-si"|]
    with
      | e -> begin
          flush stdout; flush stderr;
          raise e
      end
;;

let close_pipes (pin,pout,perr,id) : unit =
    (try
         flush pout;
         Unix.close (Unix.descr_of_out_channel pout);
         Unix.close (Unix.descr_of_in_channel perr)
     with
       | e -> () );
    (try
         Unix.close (Unix.descr_of_in_channel pin)
     with
       | e -> () )
;;

let stop (pin,pout,perr,id) (killing_signal: int)  =
    close_pipes (pin,pout,perr,id);
    try 
        Unix.kill id killing_signal;
        ignore (Unix.waitpid [] id)
    with														
      | e -> 
          (ignore e;)
;;
					
let main_fnc () =
  let _= process_cmd_line () in
  let formula= read_file !Globals.source_file in
	(* let _= print_endline (formula) in *)
  let _= print_endline (string_of_int !Globals.nums_of_check_sat) in
  let (pin,pout,perr,id)=start () in (*start z3 with interactive mode*)
  begin 
			let break = ref 0 in
      let rec helper c = 
        try
            let line = input_line c in 
            let _= print_endline (line) in
						let _= print_endline (string_of_int !break) in
						let _= break := !break + 1 in
						if (!break < !Globals.nums_of_check_sat) then 
               helper c 
						else 
							break := 0	 
        with 
          | End_of_file -> print_endline ("Reach end!!")
      in
	  	let i= ref 0 in
	  	while (!i < !Globals.n_exec) do
        let _= output_string (pout) formula in
        let _= flush (pout) in
        let _= helper pin in
			i := !i+1
	  	done; 
	  	stop (pin,pout,perr,id)
  end
;;

let main_runz3 () =
  let (set_options,formula_list,last)= read_file_2 !Globals.source_file in
  let (pin,pout,perr,id)=start () in (*start z3 with interactive mode*)
  begin 
	   	let helper chi =
              let str_list= icollect_output chi [] in
			        let _=List.map (fun x-> print_endline (x)) str_list in ()
			in
	  	let i= ref 0 in
			(* let _= output_string (pout) set_options in *)
      (* let _= flush (pout) in                     *)
      let _= output_string (pout) "(push 0)\n" in
      let _= flush (pout) in
	  	while (!i < !Globals.n_exec) do
				let _= List.map ( fun formula ->
                           let _= output_string (pout) formula in
                           let _= flush (pout) in
                           let _= helper pin in ()
			          ) formula_list
				in
		    let _= output_string (pout) last in
	      (* let _= print_endline (last) in *)
        let _= flush (pout) in	
		    let _= output_string (pout) "(pop 0)\n" in
        let _= flush (pout) in
			i := !i+1
	  	done;
	  	stop (pin,pout,perr,id)
  end
;;

let print_parse_arg () =
	let _ =
  Printf.printf "This program is named %s.\n" Sys.argv.(0);
  for i = 1 to Array.length Sys.argv - 1 do
    Printf.printf "the argument #%d is %s\n" i Sys.argv.(i)
  done
	in ()
;;

let main_generate_tests () =
  let num_vars= !Globals.num_vars_test in
	let _=
	if(Sys.argv.(1)="-gen-if-range" || Sys.argv.(1)="-gen-ifel-range") then
		(* let _= print_endline ("got here") in *)
    let i = ref !Globals.min in
	  while !i <= !Globals.num_vars_test do
		(* let _= print_endline (string_of_int !i) in	 *)
	   Generate_test.generate_test !i;
		 i := !i+ !Globals.off_set
		done; 
	else
		 (* let _= print_endline ("got else") in *)
		 Generate_test.generate_test num_vars
	in	 	
	if(num_vars >=2) then
	  let with_option= string_of_int num_vars in
		let with_else_op = if(!Globals.with_else) then "if-else" else "if" in 
	  print_endline ("Generated file in: spring/"^with_else_op^"/spring-"^with_else_op^"-"^with_option^".ss")
;;

(*-------------------Execute main here--------------------------*)
let _= process_cmd_line () in
  let _=print_parse_arg () in
  if(!Globals.num_vars_test = 0) then
     let _= main_runz3 () in ()
	else 
		 let _= main_generate_tests () in ()
(*--------------------------------------------------------------*)
			
;;
