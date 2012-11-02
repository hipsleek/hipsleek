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

let read_file_old filename = 
  (*let _= print_endline ("file:"^ !Globals.source_file) in*)
  let lines = ref "" in
  let chan = open_in filename in
  try
      while true; do
        lines := !lines ^ (input_line chan) 
      done; ""
  with End_of_file ->
      close_in chan;
      !lines
;;

let read_file filename =
  let chan = open_in filename in
  let lip= Std.input_list chan in
  let _= close_in in
  (*let _= print_endline ("file2:"^ !Globals.source_file) in *)
  List.fold_left ( fun a b->
      let _=try 
                let _= BatString.find b "(check-sat)" in
                Globals.nums_of_check_sat := !Globals.nums_of_check_sat + 1 
            with _ ->() 
      in a^"\n"^b) "" lip 
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
  (*let _= print_endline (string_of_int !Globals.nums_of_check_sat) in*)
  let (pin,pout,perr,id)=start () in (*start z3 with interactive mode*)
  begin 
      let br = ref 0 in
      let rec helper c = 
        try
            let line = input_line c in 
            let _=print_endline (line) in 
            let _= br := !br + 1 in
            if (!br < !Globals.nums_of_check_sat) then helper c
              else
              let _= print_endline("---------") in
              br := 0
        with 
          | End_of_file -> print_endline ("end")
      in
	  let i= ref 0 in
	  while (!i< !Globals.n_exec) do
        let _= output_string (pout) formula in
        let _= flush (pout) in
        let _= helper pin in
		i := !i+1
	  done; 
	  stop (pin,pout,perr,id)
  end
;;

let _= main_fnc () in ()
;;
