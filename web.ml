#include "xdebug.cppo"
module PrioQueue =
struct
  type priority = int
  type 'a queue = Empty | Node of priority * 'a * 'a queue * 'a queue
  let empty = Empty
  let rec insert queue prio elt =
    match queue with
      Empty -> Node(prio, elt, Empty, Empty)
    | Node(p, e, left, right) ->
      if prio > p
      then Node(prio, elt, insert right p e, left)
      else Node(p, e, insert right prio elt, left)
  exception Queue_is_empty
  let rec remove_top = function
      Empty -> raise Queue_is_empty
    | Node(prio, elt, left, Empty) -> left
    | Node(prio, elt, Empty, right) -> right
    | Node(prio, elt, (Node(lprio, lelt, _, _) as left),
           (Node(rprio, relt, _, _) as right)) ->
      if lprio > rprio
      then Node(lprio, lelt, remove_top left, right)
      else Node(rprio, relt, left, remove_top right)
  let extract = function
      Empty -> raise Queue_is_empty
    | Node(prio, elt, _, _) as queue -> (prio, elt, remove_top queue)
end;;



let queue : (int * int * string * Tpdispatcher.prove_type) PrioQueue.queue ref = ref PrioQueue.Empty

let cluster_locations = ref ""
let provers = ref ([]: (Unix.file_descr*(bool ref)) list) (* flag is a ref bool denoting if the underlying prover is idle*)

let all_clients = ref ([]: (Unix.file_descr*int) list) (* TODO clients need to send job with seqno -1 to close connection*)
let job_clients = ref ([]: (int*(int*out_channel)) list)
let job_no = ref 0


let listen_sock = ref (Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0)
let port = ref 8888

let prover_channels () = List.map (fun a-> (fst a)) !provers

let rec main_loop () =
  begin  

    let idle = List.filter (fun (_,flag) -> !flag) !provers in
    List.iter 
      (fun (fd,flag) -> 
         if !queue <> PrioQueue.Empty then begin
           let outc = Unix.out_channel_of_descr fd in
           print_string "job_assignment:";
           let (_,(jno,seqno,prover_arg,formula),nqueue) = PrioQueue.extract !queue in
           print_string (string_of_int(jno));
           Net.IO.write_job outc jno prover_arg formula;(* TODO data needs to be changed to accomodate seqno etc *)
           flag := false;
           queue := nqueue;
           print_endline_quiet "finished_assignment"
         end) idle;

    if !queue = PrioQueue.Empty then ignore(Unix.select (((!listen_sock)::(List.map (fun a->(fst a)) !all_clients))@(List.map (fun (fd,_) -> fd) (!provers))) [] [] (-1.)) else ();

    let (lst,_,_) = (Unix.select ((!listen_sock)::(List.map (fun a->(fst a)) !all_clients)) [] [] 0.) in
    List.iter
      (fun fd ->
         if fd = !listen_sock then begin
           let sockfd,address = Unix.accept !listen_sock in
           let () = match address with
               Unix.ADDR_INET (a,p) -> print_endline_quiet ("received connection from " ^ Unix.string_of_inet_addr(a) ^ ":" ^ string_of_int(p))
             | _ -> () in
           all_clients := (sockfd,0)::(!all_clients)
         end else begin
           let in_ch = Unix.in_channel_of_descr fd in
           let seq_no,prover_arg,formula,priority = Net.IO.read_job_web in_ch in
           if seq_no = -1 then begin
             print_endline_quiet "client closed connection";
             Unix.close fd;
             all_clients := List.remove_assoc fd (!all_clients)
           end else begin
             print_string "new job...";
             incr job_no;
             queue := PrioQueue.insert !queue priority (!job_no,seq_no,prover_arg,formula); (* TODO change priority *)
             job_clients := (!job_no,(seq_no,Unix.out_channel_of_descr fd))::(!job_clients);
             print_endline_quiet (" received "^string_of_int(!job_no))
           end
         end) lst;


    let (lst,_,_) = Unix.select (List.map (fun (fd,_) -> fd) (!provers)) [] [] 0. in
    List.iter 
      (fun fd -> let inc = (Unix.in_channel_of_descr fd) in
        let (jno,res) = Net.IO.read_result inc in
        let seqno,outclient = List.assoc jno !job_clients in
        Net.IO.write_result outclient seqno res;
        job_clients := List.remove_assoc jno !job_clients;
        (List.assoc fd (!provers)) := true) lst;

    main_loop ()
  end

let main () =
  Arg.parse [
    "--cluster",Arg.Set_string cluster_locations, "<host1:port1;host2:port2...>: Use provers at the address given";
    "--socket",Arg.Set_int port,"<port>: start the web service on the localhost at this socket";
  ]
    (fun s -> ())
    ("Usage: " ^ Sys.argv.(0) ^ "--socket [port] --cluster [cluster adresses]");
  if Unix.fork() > 0 then begin
    print_endline_quiet "Web service started.";
    exit 0
  end else begin
    ignore(Unix.setsid());
    try
      let external_host_ports =  Str.split (Str.regexp ";") !cluster_locations in
      let uniq_hp = ref [] in
      List.iter (fun hp -> if not(List.mem hp !uniq_hp) then uniq_hp := hp::!uniq_hp else ()) external_host_ports;
      List.iter (fun hp -> 
          let h_p = (Str.split (Str.regexp ":") hp) in
          let host = (List.hd h_p) in
          let port = (List.nth h_p 1) in
          if host <> Unix.gethostname () then
            ignore(Unix.system("xterm -e rsh "^host^" ~/hip/prover --socket "^port^"\\;bash &"))
          else ignore(Unix.system("xterm -e ~/hip/prover\\ --socket\\ "^port^"\\;bash &"))) !uniq_hp;
      Unix.sleep 1;
      List.iter (fun hp ->
          let sockfd = Net.Socket.init_client_fd hp in
          provers := ((sockfd,ref true)::(!provers))) external_host_ports;
      print_endline ("num of host machines = "^string_of_int(List.length external_host_ports));


      let my_addr = (Unix.gethostbyname(Unix.gethostname())).Unix.h_addr_list.(0) in
      Unix.bind !listen_sock (Unix.ADDR_INET (my_addr,!port));
      Unix.listen !listen_sock 99;



      main_loop ();
    with
    | End_of_file -> begin print_endline_quiet "END OF FILE"; exit 0 end
    | Unix.Unix_error (err, _, _) ->
      print_endline_quiet (Unix.error_message err);
  end;

;;

main ()
