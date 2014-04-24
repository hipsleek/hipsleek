(*z3-steps-test1-no-slicing-script.smt2*)
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

let start ()= 
    try
        open_process_full "z3" [|"z3";"-smt2"; "-si"|]
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
					
let formula="(push)
(declare-const x Int)
(declare-const y Int)
(declare-const x1 Int)
(declare-const y1 Int)
(declare-const res Bool)
 (push);  
   (assert (< 2 x))
   (assert (<= 0 y))
   (push) ; 
     (assert (= x1 (+ 1 x))) 
     (assert (= y1 (+ 1 y)))
     (push); 
       (assert (< 3 x1))
       (assert res)
       (check-sat)
     (pop);
     (push); 
       (assert (<= x1 3))
       (assert (not res))
       (check-sat)
     (pop); 
     (push); 
       (declare-const b_191 Bool)
       (assert (< 3 x1))
       (assert b_191)
       (assert (< 3 x1))
       (push) ; pu5
         (assert b_191)
         (check-sat)
       (pop) ; 
       (push) ; 
         (assert (not b_191)) 
         (check-sat)
       (pop) ; 
     (pop) ; 
   (pop) ; 
   (push) ; 
     (declare-const b_547 Bool)
     (assert (and (and (and (and (and (< 3 (+ 1 x)) b_547) (< 3 (+ 1 x))) b_547) (= (+ x1 (* 1 1)) (+ 1 x)))  (= y1 (+ (+ 1 1) y))))
     (push)
       (assert (not (= x1 x)))
       (check-sat)
     (pop)
     (push)
       (assert (not (< 1 y1)))
       (check-sat)
     (pop)
   (pop) ; 
 (pop) ; 
(pop);
" in
let (pin,pout,perr,id)=start () in (*start z3 with interactive mode*)
  begin 
	  let br= ref 0 in (*the numbers of check-sat*)
      let rec helper chn = 
		try
			let _= br := !br+1 in
            let line = input_line chn in
            let _=print_endline (line) in
            if(!br<6) then helper chn
			else let _= print_endline ("------") in br := 0
        with
          | _ ->  let _= print_endline ("dm") in ()
      in
	  let i= ref 0 in
	  while (!i< 1000) do
        let _= output_string (pout) formula in
		let _=flush (pout) in
		let _= helper pin in
		i := !i+1
	  done;
	  stop (pin,pout,perr,id)
  end
	  
