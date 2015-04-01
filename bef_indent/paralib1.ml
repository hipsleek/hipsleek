#include "xdebug.cppo"
open Gen.Basic

(* map_para with fork *)
let webs = ref false
    (** map_para takes an extra argument init which is a function which is called before individual evaluation of g on the list*)
    let map_para init g input_list  =
    begin    	
      let wait_for_everyone list_of_p =
        for i = 1 to List.length list_of_p do
          begin
            let mypid,mystatus = Unix.wait () in
            ignore(Unix.system ("cat stdout.txt." ^ string_of_int(mypid)));
            Sys.remove ("stdout.txt." ^ string_of_int(mypid));
          end
	    done
      in
      let list_of_pids = ref [] in
      let rec inv f mylist flag=
        match mylist with
  	    | [] -> []
  	    | head :: tail ->
  	      let input, output = Unix.pipe() in
  	      match Unix.fork() with
  	      | -1 -> begin let () = print_endline_quiet "NOT_PARALLEL" in (List.map f mylist)end
  	      | 0 ->
  	      	Unix.dup2 (Unix.openfile ("stdout.txt."^string_of_int(Unix.getpid ())) [Unix.O_WRONLY;Unix.O_CREAT] 0o666) Unix.stdout;
  	        Unix.close input;
  	        let output = Unix.out_channel_of_descr output in
  	        init ();
  	        Marshal.to_channel output (f head) [];
  	        if !webs then Net.IO.write_job_web (!Tpdispatcher.Netprover.out_ch) (-1) "" "" 1 else ();
  	        close_out output;
  	        exit 0
  	      | pid ->
  	        Unix.close output;
  	        let input = Unix.in_channel_of_descr input in
  	        let b = (inv f tail false) in
  	        let () = (list_of_pids := (pid::!list_of_pids)) in
  	        let a = (Marshal.from_channel input) in
  	        close_in input;
  	        if flag then begin 
  	          (wait_for_everyone !list_of_pids); 
  	          if !webs then Net.IO.write_job_web (!Tpdispatcher.Netprover.out_ch) (-1) "" "" 1 else ()
  	        end else ();
            a :: b
      in
      inv g input_list true
    end
