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
					 let line = input_line chn in (*if the last result is unknown => lead to timeout of collecting output*)
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
  let list_check = ref ([]:(string) list) in
  let chan = open_in filename in
  try
      while true; do
        let b = input_line chan in
					let _=lines := !lines^b^"\n" in
					(* let _=print_endline (b) in *)
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
			([],"")
  with End_of_file ->
		begin	
      close_in chan;
			(* let _= List.map (fun x-> print_endline (x)) !list_check in *)
      (!list_check,!lines)
	  end		
;;

let incr_nums_check_sat ()=
	  Globals.nums_of_check_sat := !Globals.nums_of_check_sat + 1 	 

;;		
let count_num_check_sat str =
      try 
         let ic= BatString.find str "(check-sat)" in
				 try
						 let ise= BatString.find str ";" in	
				     if (ic < ise) then incr_nums_check_sat ()     	     
				 with _ -> incr_nums_check_sat ()
      with _-> ()
;;

let read_file_boogie filename = 
    (*let _= print_endline ("file:"^ !Globals.source_file) in*)
  let lines = ref "" in
	let first_push = ref false in
  let first_decl = ref "" in
  let chan = open_in filename in
  try
      while true; do
        let b = input_line chan in
					(* let _=print_endline (b) in *)
					if(not !first_push) then
           try 
             let ic= BatString.find b "(push" in
				     try
						   let ise= BatString.find b ";" in	
				       if (ic < ise) then
								begin 
									first_push := true;
								  first_decl := !lines;
									lines := b
								end   	     
				     with _ ->
							let _= first_push := true in 
							let _=first_decl := !lines in lines := b    	    
					with _->	
						let _= lines := !lines^b^"\n" in
							count_num_check_sat b
					else
						let _= lines := !lines^b^"\n" in
						  count_num_check_sat b
      done; 
      close_in chan;
			("","")
  with End_of_file ->
		begin	
      close_in chan;
			(* let _= List.map (fun x-> print_endline (x)) !list_check in *)
      (!first_decl,!lines)
	  end
;;


let get_result_file filename =
  let chan = open_in filename in
  let lip= Std.input_list chan in
  let _= close_in in
	let accumulate = ref [] in
	let num_timeout = ref 0 in
  (*let _= print_endline ("file2:"^ !Globals.source_file) in *)
	let flag= ref false in
  let _= List.map ( fun x->
		(* let _=print_endline (x) in *)
		let _=try
			BatString.find x "Fail. (timeout)";
		  num_timeout := !num_timeout +1
			with _->() in 
		if(!flag = false) then
		  try 
			  BatString.find x "Stop";
			  flag := true
		  with _-> ()
		else	
			try
			  BatString.find x "real";
			  flag := false
		  with _->
			(* let _= print_endline (x) in *)
			(* let _= print_endline (filename) in *)
				accumulate := !accumulate @ [x]
		) lip 
	in
	 (!accumulate,!num_timeout) 
		
;;

let get_result_file_spring filename =
  let chan = open_in filename in
  let lip= Std.input_list chan in
  let _= close_in in
	let accumulate = ref [] in
	let num_timeout = ref 0 in
	let num_schedule = ref "" in
  (*let _= print_endline ("file2:"^ !Globals.source_file) in *)
	let flag= ref false in
  let _= List.map ( fun x->
		(* let _=print_endline (x) in *)
		 try (*NO cast*)
									BatString.find x "goals scheduled";
									num_schedule :=  BatString.strip ~chars:"[wp] , goals scheduled" x;
		 with _->
		let _=try
			BatString.find x "Error: Failure(\"timeout\")";
		  num_timeout := !num_timeout +1
			with _->() in 
		if(!flag = false) then
		  try 
			  BatString.find x "Total time:";
			  flag := true
		  with _-> ()
		else	
			try
			  BatString.find x "real";
			  flag := false
		  with _->
			(* let _= print_endline (x) in *)
			(* let _= print_endline (filename) in *)
				accumulate := !accumulate @ [x]
		) lip 
	in
	 (!accumulate,!num_timeout,int_of_string !num_schedule) 
		
;;

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
  let (formula_list,last)= read_file_2 !Globals.source_file in
  let (pin,pout,perr,id)=start () in (*start z3 with interactive mode*)
  begin 
	   	let helper chi =
              let str_list= icollect_output chi [] in
			        let _=List.map (fun x-> print_endline (x)) str_list in ()
			in
	  	let i= ref 0 in
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

let main_run_boogie () =
  let (first_decl,body)= read_file_boogie !Globals.source_file in
	(* let _=print_endline (first_decl) in *)
	(* let _=print_endline (body) in       *)
  let (pin,pout,perr,id)=start () in (*start z3 with interactive mode*)
  begin 
	   	let helper chi =
              let str_list= icollect_output chi [] in
			        let _=List.map (fun x-> print_endline (x)) str_list in ()
			in
	  	let i= ref 0 in
      let _= output_string (pout) first_decl in
      let _= flush (pout) in
	  	while (!i < !Globals.n_exec) do
				    let _= output_string (pout) "(push 1)" in
            let _= output_string (pout) body in
            let _= output_string (pout) "(pop 1)" in
            let _= flush (pout) in	
						for j=0 to !Globals.nums_of_check_sat-1 do
            let _= helper pin in () 
						done;
			i := !i+1
	  	done;
	  	stop (pin,pout,perr,id)
  end
;;


let main_generate_tests () =
  let num_vars= !Globals.num_vars_test in
	if(!Globals.use_imp)&& not !Globals.use_boogie then
		let _=Generate_imp_test.generate_test num_vars in
	  ()
	else
	  let _=Generate_test.generate_test num_vars in
	  print_endline ("Generated file in: spring/spring-"^(string_of_int num_vars)^".ss")
;;

let get_result res_file middle_fix=
	let filename= if(!Globals.logs_dir <>"") then 
		ref ("./experiments/"^(!Globals.logs_dir)^"/spaguetti.")
		else 
		ref ("./experiments/logs_Nov13_0032/spaguetti.")	 
	in
	let out_stream = open_out res_file in
	let ll= Array.make 11 "" in
    (*let _ = print_endline ("input: " ^ input) in*)
	for i=10 to 20 do (*NO SLICING*)
     	let l1,t1=get_result_file (!filename^middle_fix^(string_of_int i)^"."^ !Globals.tp) in
			let l2,t2=get_result_file (!filename^middle_fix^(string_of_int i)^"."^ !Globals.tp^"c") in
			let resi= ref "" in
			let temp = ref "" in	
			let _= List.map ( fun x-> 
				          (* let _= 	print_endline (x) in *)
				          try (*NO cast*)
									BatString.find x "Time spent in main process: ";
									resi := !resi ^ BatString.strip ~chars:"\tTime spent in main process: , second(s)" x;
									(* print_endline (!resi); *)
									(* output_string out_stream (s^"\t");  *)
									resi := !resi^"\t"
									with _->
										try
											BatString.find x "Time spent in child processes: ";
									    resi := !resi^ BatString.strip ~chars:"\tTime spent in child processes: , second(s)" x;
											ll.(i-10) <- !resi;
												(* print_endline (!resi^ "--"^string_of_int i) *)
									     (* output_string out_stream (s^"\t");  *)
											with _-> ()
				) l1 in (*CAST*)
					(* print_endline (string_of_int i) *)
			let _= resi:= "" in
			let _= List.map ( fun x->
				          try (*NO cast*)
									BatString.find x "SAT Count   : ";
									resi := BatString.strip ~chars:"SAT Count   : , " x;
									(* output_string out_stream (s^"\t");  *)
									resi := !resi ^"\t"
									with _->
										try
											BatString.find x "SAT % Hit   : ";
									    resi := !resi ^(BatString.strip ~chars:"SAT % Hit   : ,%" x);
										resi := !resi ^"\t";
									     (* output_string out_stream (s^"\t");  *)
											with _->
													try
											BatString.find x "IMPLY Count : ";
									    resi := !resi ^BatString.strip ~chars:"IMPLY Count : , " x ;
											resi := !resi ^"\t";
									
											with _->
													try
											BatString.find x "IMPLY % Hit : ";
									    resi :=  !resi^ BatString.strip ~chars:"IMPLY % Hit : ,%" x ;
											resi := !resi ^"\t";
										
											with _->
													try
											BatString.find x "Time(cache overhead) : ";
									    resi := !resi ^ BatString.strip ~chars:"Time(cache overhead) : , (seconds)" x ;
											resi := !resi ^"\t";
											
											with _->
											 try
									BatString.find x "Time spent in main process: ";
									temp :=   BatString.strip ~chars:"\tTime spent in main process: , second(s)" x ;
								  temp := !temp ^ "\t"
									with _->
										try
											BatString.find x "Time spent in child processes: ";
									    temp:= !temp ^ BatString.strip ~chars:"\tTime spent in child processes: , second(s)" x   ;
											resi := "\t"^ !temp ^"\t"^ !resi ^string_of_int t1 ^"\t" ^string_of_int t2;
							
											ll.(i-10) <- (ll.(i-10) ^ !resi ^ "\n");
											print_endline (ll.(i-10));
											print_endline ("Test: "^string_of_int i);
											with _-> ()
												
				) l2 in ()
	done;
	for i=0 to 10 do
		 output_string out_stream (ll.(i));
	done;	
 close_out out_stream;
;;

let get_result_spring res_file n=
	let filename= if(!Globals.logs_dir <>"") then 
		ref ("./"^(!Globals.logs_dir)^"/spring.")
		else 
		ref ("./experiments/logs_Nov14_0959/spring.")	 
	in
	let ll1= Array.make (n-1) "" in
	let ll2= Array.make (n-1) "" in
    (*let _ = print_endline ("input: " ^ input) in*)
	for i=2 to n do (*NO SLICING*)
     	let l1,t1,nums1=get_result_file_spring (!filename^(string_of_int i)^".s") in
			let l2,t2,nums2=get_result_file_spring (!filename^(string_of_int i)^".ss") in
			let resi= ref "" in
			let temp = ref "" in	
			let _= List.map ( fun x-> 
				          (* let _= 	print_endline (x) in *)
				          try (*NO cast*)
									BatString.find x "Main: ";
									resi := !resi ^ BatString.strip ~chars:"Main: , " x;
									(* print_endline (!resi); *)
									(* output_string out_stream (s^"\t");  *)
									resi := !resi^"\t"
									with _->
										try
											BatString.find x "Child: ";
									    resi := !resi^ BatString.strip ~chars:"Child: , " x;
											ll1.(i-2) <- !resi^"\t"^string_of_int t1^"\t"^string_of_int nums1^"\n";
												(* print_endline (!resi^ "--"^string_of_int i) *)
									     (* output_string out_stream (s^"\t");  *)
											with _-> ()
				) l1 in (*CAST*)
					(* print_endline (string_of_int i) *)
			let _= resi:= "" in
			let _= List.map ( fun x->
				          (* let _= 	print_endline (x) in *)
				          try (*NO cast*)
									BatString.find x "Main: ";
									resi := !resi ^ BatString.strip ~chars:"Main: , " x;
									(* print_endline (!resi); *)
									(* output_string out_stream (s^"\t");  *)
									resi := !resi^"\t"
									with _->
										try
											BatString.find x "Child: ";
									    resi := !resi^ BatString.strip ~chars:"Child: , " x;
											ll2.(i-2) <- !resi^"\t"^string_of_int t2^"\t"^string_of_int nums2^"\n";
												(* print_endline (!resi^ "--"^string_of_int i) *)
									     (* output_string out_stream (s^"\t");  *)
											with _-> ()
												
				) l2 in ()
	done;
	let out_stream = open_out (res_file^".s") in
	for i=0 to n-2 do
		 output_string out_stream (ll1.(i));
	done;	
 close_out out_stream;
 let out_stream = open_out (res_file^".ss") in
	for i=0 to n-2 do
		 output_string out_stream (ll2.(i));
	done;	
 close_out out_stream;

;;

let main_get_result ()= 
 if (!Globals.tp<>"spring") then	
  let _ = get_result "norm.result" "" in 
  let _ = get_result "ns.result" "efp.ns." in
  let _ = get_result "ans.result" "efp.ans." in
  let _ = get_result "aus.result" "efp.aus." in ()
 else
	let _=get_result_spring "result" !Globals.sp in ()
	
;;
(*-------------------Execute main here--------------------------*)
let _= process_cmd_line () in
  if(!Globals.num_vars_test = 0) then
		if(!Globals.run_boogie) then
			let _= main_run_boogie () in ()
		else if(!Globals.get_result) then
			let _= main_get_result () in ()	
		else	
      let _= main_runz3 () in ()
	else 
		 let _= main_generate_tests () in ()
(*--------------------------------------------------------------*)
			
;;
