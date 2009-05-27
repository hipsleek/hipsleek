external set_close_on_exec : Unix.file_descr -> unit = "unix_set_close_on_exec";;

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
          begin try Unix.execv cmd args
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

let open_proc cmd args out_file:int  =
  match Unix.fork() with
  |  0 -> begin 
			let output = Unix.openfile out_file [Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
			Unix.dup2 output Unix.stdout; Unix.close output;
			try Unix.execv cmd args with _ -> exit 127 end
  | id -> id
;;