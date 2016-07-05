#include "xdebug.cppo"
open Gen.Basic

(* map_para with fork and limited number of processes *)
let webs = ref false
let map_para_net init g input_list max =
  let running = ref 0 in
  let list_of_pids = ref [] in
  let next_machines = ref !Tpdispatcher.external_host_ports in
  let pid_machine = ref [] in
  let answer_list = ref [] in
  let success_wait = ref [] in
  let rec inv f mylist =
    match mylist with
    | [] -> ()
    | head :: tail ->
      let input, output = Unix.pipe() in
      let machine = (List.hd (!next_machines)) in
  	  match Unix.fork() with
  	  | -1 ->let () = print_endline_quiet "NOT_PARALLEL" in 
  	         ignore(List.map f mylist)
  	  | 0 ->
  	    begin
  	      Tpdispatcher.Netprover.set_use_socket_map machine;
  	      let () = Unix.dup2 (Unix.openfile ("stdout.txt."^string_of_int(Unix.getpid ())) [Unix.O_WRONLY;Unix.O_CREAT] 0o666) Unix.stdout in 
  	      let todo_unk = Unix.close input in
  	      let output = Unix.out_channel_of_descr output in
  	      init ();
  	      Marshal.to_channel output (f head) [];
  	      if !webs then Net.IO.write_job_web (!Tpdispatcher.Netprover.out_ch) (-1) "" "" 1 else ();
  	      close_out output;
  	      exit 0
  	    end
  	  | pid ->
  	    begin
  	        ignore(match !next_machines with 
  	        | head::[] -> begin
  	          pid_machine := (pid,head) :: !pid_machine;
  	          next_machines := !Tpdispatcher.external_host_ports
  	          end
  	        | head::tail -> begin 
  	          pid_machine := (pid,head) :: !pid_machine;
  	          next_machines := tail 
  	          end
  	        | [] -> failwith "next_machine list error");
  	      
  	      incr running;
  	      Unix.close output;
  	      list_of_pids := ((pid,input)::(!list_of_pids));
  	      (if !running < max then begin
  	        ignore(inv f tail)
          end else begin
            let mypid,mystatus = Unix.wait () in
            let input1 = List.assoc mypid (!list_of_pids) in
            let input1 = Unix.in_channel_of_descr input1 in
            let ans = (Marshal.from_channel input1) in
            let aflag = ref true in
            success_wait := mypid :: (!success_wait);
            next_machines := (List.assoc mypid !pid_machine) :: !next_machines;
            ignore(Unix.system ("cat stdout.txt." ^ string_of_int(mypid)));
            Sys.remove ("stdout.txt." ^ string_of_int(mypid));
            answer_list := (mypid,ans) :: (!answer_list);
            close_in input1;
            running := (!running) - 1;
            (while !aflag do
            begin
              try 
              let mypid,status = Unix.waitpid [Unix.WNOHANG] (-1) in
              (if mypid = 0 then aflag := false 
              else begin 
                let input1 = List.assoc mypid (!list_of_pids) in
                let input1 = Unix.in_channel_of_descr input1 in
                let ans = (Marshal.from_channel input1) in
                answer_list := (mypid,ans) :: (!answer_list);
                success_wait := mypid :: (!success_wait);
                next_machines := (List.assoc mypid !pid_machine) :: !next_machines;
                ignore(Unix.system ("cat stdout.txt." ^ string_of_int(mypid)));
                Sys.remove ("stdout.txt." ^ string_of_int(mypid));
                close_in input1;
                running := (!running) - 1
                end) with Unix.Unix_error (Unix.ECHILD,str1,str2) -> aflag := false
            end
            done);
            inv f tail
          end);
          if (not (List.exists (fun n -> n = pid) (!success_wait))) then begin
  	        let input = Unix.in_channel_of_descr input in
  	        let ans = (Marshal.from_channel input) in
  	        let () = ignore(Unix.waitpid [] pid) in
  	        success_wait := pid :: (!success_wait);
  	        next_machines := (List.assoc pid !pid_machine) :: !next_machines;
  	        running := (!running) - 1;
  	        ignore(Unix.system ("cat stdout.txt." ^ string_of_int(pid)));
            Sys.remove ("stdout.txt." ^ string_of_int(pid));
  	        answer_list := (pid,ans)::(!answer_list);
  	        close_in input
  	      end else ()
        end
  in
  (* let rec reorder id_list ans_list =
    match id_list with 
    | [] -> []
    | head :: tail ->
      (List.assoc (fst head) ans_list) :: (reorder tail ans_list)
  in  *)
  inv g input_list;	
  if !webs then 
    Net.IO.write_job_web (!Tpdispatcher.Netprover.out_ch) (-1) "" "" 1
  else ();
  let rec print_output lpid = 
    match lpid with
    | [] -> ()
    | head :: tail ->
      begin
      (* ignore(Unix.system ("cat stdout.txt." ^ string_of_int(head)));
      Sys.remove ("stdout.txt." ^ string_of_int(head)); *)
      print_output tail
      end
  in
  print_output !success_wait;
  !answer_list
  (* reorder (!list_of_pids) (!answer_list) *)
;;

let map_para init g input_list max =	
  let running = ref 0 in
  let list_of_pids = ref [] in
  let answer_list = ref [] in
  let success_wait = ref [] in
  let rec inv f mylist =
    match mylist with
    | [] -> ()
    | head :: tail ->
      let input, output = Unix.pipe() in
  	  match Unix.fork() with
  	  | -1 -> begin let () = print_endline_quiet "NOT_PARALLEL" in ignore(List.map f mylist) end
  	  | 0 ->
  	    begin
  	      let () = Unix.dup2 (Unix.openfile ("stdout.txt."^string_of_int(Unix.getpid ())) [Unix.O_WRONLY;Unix.O_CREAT] 0o666) Unix.stdout in 
  	      let todo_unk = Unix.close input in
  	      let output = Unix.out_channel_of_descr output in
  	      init ();
  	      Marshal.to_channel output (f head) [];
  	      close_out output;
  	      exit 0
  	    end
  	  | pid ->
  	    begin
  	      running := (!running) + 1;
  	      Unix.close output;
  	      list_of_pids := ((pid,input)::(!list_of_pids));
  	      (if !running < max then begin
  	        ignore(inv f tail)
          end else begin
            let mypid,mystatus = Unix.wait () in
            let input1 = List.assoc mypid (!list_of_pids) in
            let input1 = Unix.in_channel_of_descr input1 in
            let ans = (Marshal.from_channel input1) in
            let aflag = ref true in
            success_wait := mypid :: (!success_wait);
            ignore(Unix.system ("cat stdout.txt." ^ string_of_int(mypid)));
            Sys.remove ("stdout.txt." ^ string_of_int(mypid));
            answer_list := (mypid,ans) :: (!answer_list);
            close_in input1;
            running := (!running) - 1;
            (while !aflag do
            begin
              try 
              let mypid,status = Unix.waitpid [Unix.WNOHANG] (-1) in
              (if mypid = 0 then aflag := false 
              else begin 
                let input1 = List.assoc mypid (!list_of_pids) in
                let input1 = Unix.in_channel_of_descr input1 in
                let ans = (Marshal.from_channel input1) in
                answer_list := (mypid,ans) :: (!answer_list);
                success_wait := mypid :: (!success_wait);
                ignore(Unix.system ("cat stdout.txt." ^ string_of_int(mypid)));
                Sys.remove ("stdout.txt." ^ string_of_int(mypid));
                close_in input1;
                running := (!running) - 1
                end) with Unix.Unix_error (Unix.ECHILD,str1,str2) -> aflag := false
            end
            done);
            inv f tail
          end);
          if (not (List.exists (fun n -> n = pid) (!success_wait))) then begin
  	        let input = Unix.in_channel_of_descr input in
  	        let ans = (Marshal.from_channel input) in
  	        let () = ignore(Unix.waitpid [] pid) in
  	        success_wait := pid :: (!success_wait);
  	        running := (!running) - 1;
  	        ignore(Unix.system ("cat stdout.txt." ^ string_of_int(pid)));
            Sys.remove ("stdout.txt." ^ string_of_int(pid));
  	        answer_list := (pid,ans)::(!answer_list);
  	        close_in input
  	      end else ()
        end
  in
  (* let rec reorder id_list ans_list =
    match id_list with 
    | [] -> []
    | head :: tail ->
      (List.assoc (fst head) ans_list) :: (reorder tail ans_list)
  in  *)
  inv g input_list;
  let rec print_output lpid = 
    match lpid with
    | [] -> ()
    | head :: tail ->
      begin
      (* ignore(Unix.system ("cat stdout.txt." ^ string_of_int(head)));
      Sys.remove ("stdout.txt." ^ string_of_int(head)); *)
      print_output tail
      end
  in
  print_output !success_wait;
  !answer_list
  (* reorder (!list_of_pids) (!answer_list) *)
;;
