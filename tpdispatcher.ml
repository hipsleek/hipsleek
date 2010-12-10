(*

  Choose with theorem prover to prove formula
*)

open Globals
module CP = Cpure
module MCP = Mcpure

type tp_type =
  | OmegaCalc
  | CvcLite
  | Cvc3
  | CO (* CVC Lite then Omega combination *)
  | Isabelle
  | Mona
  | OM
  | OI
  | SetMONA
  | CM (* CVC Lite then MONA *)
  | Coq
  | Z3
  | Redlog
  | RM (* Redlog and Mona *)

let tp = ref OmegaCalc
let proof_no = ref 0

type prove_type = Sat of CP.formula | Simplify of CP.formula | Imply of CP.formula * CP.formula
type result_type = Timeout | Result of string | Failure of string

let print_pure = ref (fun (c:CP.formula)-> Cprinter.string_of_pure_formula c(*" printing not initialized"*))

let sat_cache = ref (Hashtbl.create 200)
let impl_cache = ref (Hashtbl.create 200)

let prover_arg = ref "omega"
let external_prover = ref false
let external_host_ports = ref []
let webserver = ref false
let priority = ref 1
let decr_priority = ref false
let set_priority = ref false
let prio_list = ref []

module Netprover = struct
  let debuglevel = 0 
  let trace f s = if debuglevel <= 1 then (prerr_string (Printf.sprintf "\n%d: %s: %s" (Unix.getpid ()) f s); flush stderr) else ()
  let show_info f s = if debuglevel <= 2 then (prerr_string (Printf.sprintf "\n%d: %s: %s" (Unix.getpid ()) f s); flush stderr) else ()
  
  (* server-setting (prover-setting) -> ()                                 *)
  (* proc_group(reqid,[[task]],timeout) -> [result]                        *)
  (* proc_group_async(reqid,[[task]]) -> groupid                           *)
  (* wait(groupid,[taskid::int],timeout) -> [result] timeout of -1 :       *)
  (* indefinite kill(groupid,[taskid])                                     *)
  (* wait_and_kill(groupid,[taskid::int],timeout) -> [result] timeout of   *)
  (* -1 : indefinite                                                       *)
  let use_pipe = ref false
  let in_ch = ref stdin
  let out_ch = ref stdout
  let default_pipe = "default"
  let default_timeout = 200.0
  let seq_number = ref 0 (* for asynch calls in the future *)
  let get_seq_no () = incr seq_number; !seq_number
  
  let start_prover_process () =
    let is_running cmd_args =
      let cmd = "ps -u$USER -f" in
      let ch = Unix.open_process_in cmd in
      try
        let re = Str.regexp_string cmd_args in
        while true do
          let s = input_line ch in
          try
            if Str.search_forward re s 0 >= 0 then raise Exit
          with Not_found -> ()
        done;
        false
      with Exit -> true
      | End_of_file -> false
      | e -> print_string "ho"; flush stdout; false
    in
    let cmd_args = "prover --pipe " ^ default_pipe in
    if not (is_running cmd_args) then begin
      print_string "\nLaunching default prover\n."; flush stdout;
      ignore(Unix.system cmd_args)
    end
  
  let set_use_pipe () =
    start_prover_process ();
    external_prover := true;
    use_pipe := true;
    let i, o = Net.Pipe.init_client default_pipe in
    in_ch := i; out_ch := o
  
  let set_use_socket host_port =
    external_prover := true ;
    use_pipe := false;
    let i, o = Net.Socket.init_client host_port in
    in_ch := i; out_ch := o
  
	let set_use_socket_map host_port =
		external_prover := true ;
		use_pipe := false;
		let i, o = Net.Socket.init_client host_port in
		in_ch := i; out_ch := o
		
	let set_use_socket_for_web host_port =
	    external_host_ports := [host_port];
	    external_prover := true;
	    use_pipe := false;
	    let i, o = Net.Socket.init_client host_port in
		in_ch := i; out_ch := o
		
	let set_prio_list str =
	  try
	    set_priority := true;
	    let lst = Str.split (Str.regexp ";") str in
	    prio_list := List.map (fun name_prio -> let l = Str.split (Str.regexp ":") name_prio in ((List.hd l),int_of_string(List.nth l 1))) lst
	  with e -> print_endline "set_prio_list error"; raise e
 
  let index_of elem lst =
    (** return the first index of [elem] in the list [lst] *)
    let rec find i elem lst =
      match lst with
      | [] -> (- 1)
      | hd:: tl -> if elem = hd then i else find (i + 1) elem tl
    in find 0 elem lst
  
  exception ServerTimeout
  exception ParStop
  
  type pmap_result = One of string | All of string list | Unknown
  
  let pmap (provers: string) (jobs: prove_type list) (stopper: result_type -> bool) : pmap_result =
    (* [pmap] sends the tuple of [provers] and [jobs] list to the server   *)
    (* and wait for results. When a result arrives, the [stopper] function *)
    (* is applied to the result. If [stopper] returns true, the function   *)
    (* exits with the result arrives. Otherwise it continues until all of  *)
    (* the results arrives and return the whole list of results.           *)
    
    let send_stop seqno = Net.IO.write !out_ch (Net.IO.msg_type_cancel_job, seqno) in
    (* send out job list to server *)
    let seqno = get_seq_no () in
    (* let stopper_closure = Marshal.to_string stopper [Marshal.Closures] in   *)
    (* trace "closure=" stopper_closure;                                       *)
    Net.IO.write_job_to_master !out_ch seqno default_timeout provers jobs "true";
    
    (* collect the results *)
    let num_jobs = List.length jobs in
    let result_arr = Array.make num_jobs "" in
    let time_start = Unix.gettimeofday () in
    try
      let num_results = ref 0 in
      let wait_fd = Unix.descr_of_in_channel !in_ch in
      while !num_results < num_jobs do
        let time_left = default_timeout -. ((Unix.gettimeofday ()) -. time_start) in
        if time_left < 0. then
          failwith "timeout" 
        else begin
          (* show_info "pmap" (Printf.sprintf "wait %d results" (num_jobs -          *)
          (* !num_results));                                                         *)
          let in_fds, _, _ = Unix.select [wait_fd] [] [] time_left in
          if in_fds <> [] then begin
            incr num_results;
            let seqno, idx, result = Net.IO.read_result (Unix.in_channel_of_descr (List.hd in_fds)) in
            match result with
            | Result s ->
                if idx >= 0 then begin
                  (* trace "pmap" (Printf.sprintf "idx = %d" idx); *)
                  let res = Net.IO.from_string s in
                  Array.set result_arr idx s;
                  if stopper res then begin
                    show_info "pmap: discard others" "";
                    send_stop seqno;
                    Array.set result_arr 0 s; (* will return the first element only *)
                    raise ParStop
                  end
                end else
                  show_info "pmap result" "index is negative"
            | Timeout -> trace "pmap result" " timed out."
            | Failure s -> trace "pmap result" s
          end;
        end
      done;
      All (List.filter (fun s -> s <> "") (Array.to_list result_arr))
    with
    | ParStop -> trace "pmap" "\n by stoper."; (One result_arr.(0))
    | ServerTimeout -> trace "pmap" "\npmap timed out."; Unknown
    | e -> trace "pmap" (Printexc.to_string e); Unknown
  
	

    (* replaced with dileep's version above
	let call_prover (data : prove_type) =
    
	  try
		let _ = if !webserver then 
		          Net.IO.write_job_web !out_ch 0 !prover_arg data !priority 
		        else Net.IO.write_job !out_ch 0 !prover_arg data 
		in
		let _ = if !decr_priority then decr priority else () in
		let seq, result = Net.IO.read_result !in_ch in
			Net.IO.from_string result 
	  with e -> print_endline "callprover error"; raise e *)
  let call_prover ( f : prove_type) = 
    (** send message to external prover to get the result. *)
    try
      let ret = pmap !prover_arg [f] (fun _ -> false) in
      match ret with Unknown -> None 
      | One s ->   if s <> "" then Some (Net.IO.from_string s) else None
      | All results -> let s = (List.hd results) in
        if s <> "" then Some (Net.IO.from_string s) else None
    with e -> trace "pmap" (Printexc.to_string e); None
   
end

let set_tp tp_str =
  prover_arg := tp_str;  
  if tp_str = "omega" then
	tp := OmegaCalc
  else if tp_str = "cvcl" then 
	tp := CvcLite
  else if tp_str = "cvc3" then 
	tp := Cvc3
  else if tp_str = "co" then
	tp := CO
  else if tp_str = "isabelle" then
	tp := Isabelle
  else if tp_str = "mona" then
	tp := Mona
  else if tp_str = "om" then
	tp := OM
  else if tp_str = "oi" then
	tp := OI
  else if tp_str = "set" then
	tp := SetMONA
  else if tp_str = "cm" then
	tp := CM
  else if tp_str = "coq" then
	tp := Coq
  else if tp_str = "z3" then 
	tp := Z3
  else if tp_str = "redlog" then
    tp := Redlog
  else if tp_str = "rm" then
    tp := RM
  else if tp_str = "prm" then
    (Redlog.is_presburger := true; tp := RM)
  else
	()

let omega_count = ref 0

(* Method checking whether a formula contains bag constraints *)

let is_bag_b_constraint bf = match bf with
    | CP.BConst _ 
    | CP.BVar _
    | CP.Lt _ 
    | CP.Lte _ 
    | CP.Gt _ 
    | CP.Gte _
    | CP.EqMax _ 
    | CP.EqMin _
    | CP.ListIn _ 
    | CP.ListNotIn _
    | CP.ListAllN _ 
    | CP.ListPerm _
        -> Some false
    | CP.BagIn _ 
    | CP.BagNotIn _
    | CP.BagMin _ 
    | CP.BagMax _
    | CP.BagSub _
        -> Some true
    | _ -> None

let is_bag_constraint (e: CP.formula) : bool =  
  let f_e e = match e with
    | CP.Bag _
    | CP.BagUnion _
    | CP.BagIntersect _
    | CP.BagDiff _ 
        -> Some true
    | _ -> Some false
  in
  let or_list = List.fold_left (||) false in
  CP.fold_formula e (nonef, is_bag_b_constraint, f_e) or_list

let rec is_memo_bag_constraint (f:MCP.memo_pure): bool = 
  List.exists (fun c-> 
      (List.exists is_bag_constraint c.MCP.memo_group_slice)|| 
      (List.exists (fun c-> match is_bag_b_constraint c.MCP.memo_formula with | Some b-> b |_ -> false) c.MCP.memo_group_cons)
  ) f

  (* Method checking whether a formula contains list constraints *)
 
let is_list_b_formula bf = match bf with
    | CP.BConst _ 
    | CP.BVar _
    | CP.Lt _ 
    | CP.Lte _ 
    | CP.Gt _ 
    | CP.Gte _
    | CP.EqMax _ 
    | CP.EqMin _
    | CP.BagIn _ 
    | CP.BagNotIn _
    | CP.BagMin _ 
    | CP.BagMax _
    | CP.BagSub _
        -> Some false
    | CP.ListIn _ 
    | CP.ListNotIn _
    | CP.ListAllN _ 
    | CP.ListPerm _
        -> Some true
    | _ -> None
 
let is_list_constraint (e: CP.formula) : bool =
 
  let f_e e = match e with
    | CP.List _
    | CP.ListCons _
    | CP.ListHead _
    | CP.ListTail _
    | CP.ListLength _
    | CP.ListAppend _
    | CP.ListReverse _ 
        -> Some true
    | _ -> Some false
  in
  let or_list = List.fold_left (||) false in
  CP.fold_formula e (nonef, is_list_b_formula, f_e) or_list
  
let rec is_memo_list_constraint (f:MCP.memo_pure): bool = 
  List.exists (fun c-> 
      (List.exists is_list_constraint c.MCP.memo_group_slice)|| 
      (List.exists (fun c-> match is_list_b_formula c.MCP.memo_formula with | Some b-> b| _ -> false) c.MCP.memo_group_cons)
  ) f  
  
let is_mix_bag_constraint f = match f with
  | MCP.MemoF f -> is_memo_bag_constraint f
  | MCP.OnePF f -> is_bag_constraint f

let is_mix_list_constraint f = match f with
  | MCP.MemoF f -> is_memo_list_constraint f
  | MCP.OnePF f -> is_list_constraint f  
  
let elim_exists_flag = ref true
let filtering_flag = ref true

let elim_exists (f : CP.formula) : CP.formula =
  let ef = if !elim_exists_flag then CP.elim_exists f else f in
  ef

let filter (ante : CP.formula) (conseq : CP.formula) : (CP.formula * CP.formula) =
  if !filtering_flag then
	let fvar = CP.fv conseq in
	let new_ante = CP.filter_var ante fvar in
	  (new_ante, conseq)
  else
	(ante, conseq)

(* rename variables for better caching of formulas *)
let simplify_var_name (e: CP.formula) : CP.formula =
  let shorten_sv (CP.SpecVar (typ, name, prm)) vnames =
    let short_name =
      try
        Hashtbl.find vnames name
      with Not_found ->
        let fresh_name = "v" ^ (string_of_int (Hashtbl.length vnames)) in
        let _ = Hashtbl.add vnames name fresh_name in
        fresh_name
    in
    CP.SpecVar (typ, short_name, prm)
  in
  let f_bf vnames bf = match bf with
    | CP.BVar (sv, l) -> Some (CP.BVar (shorten_sv sv vnames, l))
    | _ -> None
  in
  let f_e vnames e = match e with
    | CP.Var (sv, l) ->
        Some (CP.Var (shorten_sv sv vnames, l))
    | _ -> None
  in
  let rec simplify f0 vnames = match f0 with
    | CP.Forall (sv, f1, lbl, l) ->
        let nsv = shorten_sv sv vnames in
        let nf1 = simplify f1 vnames in
        CP.Forall (nsv, nf1, lbl, l)
    | CP.Exists (sv, f1, lbl, l) ->
        let nsv = shorten_sv sv vnames in
        let nf1 = simplify f1 vnames in
        CP.Exists (nsv, nf1, lbl, l)
    | CP.And (f1, f2, l) ->
        let nf1 = simplify f1 vnames in
        let nf2 = simplify f2 vnames in
        CP.And (nf1, nf2, l)
    | CP.Or (f1, f2, lbl, l) ->
        let nf1 = simplify f1 vnames in
        let nf2 = simplify f2 vnames in
        CP.Or (nf1, nf2, lbl, l)
    | CP.Not (f1, lbl, l) ->
        CP.Not (simplify f1 vnames, lbl, l)
    | CP.BForm (bf, lbl) ->
        CP.BForm (CP.map_b_formula_arg bf vnames (f_bf, f_e) (idf2, idf2), lbl)
  in
  simplify e (Hashtbl.create 100)

let tp_is_sat_no_cache (f : CP.formula) (sat_no : string) =
  match !tp with
  | OmegaCalc ->
      begin
        (Omega.is_sat f sat_no);
      end
  | CvcLite -> Cvclite.is_sat f sat_no
  | Cvc3 -> Cvc3.is_sat f sat_no
  | Z3 -> Smtsolver.is_sat f sat_no
  | Isabelle -> Isabelle.is_sat f sat_no
  | Coq -> Coq.is_sat f sat_no
  | Mona -> Mona.is_sat f sat_no
  | CO -> 
      begin
        let result1 = (Cvclite.is_sat_raw f sat_no) in
        match result1 with
        | Some f -> f
        | None ->
            omega_count := !omega_count + 1;
            (Omega.is_sat f sat_no)
      end
  | CM -> 
      begin
        if (is_bag_constraint f) then
          (Mona.is_sat f sat_no)
        else
          let result1 = (Cvclite.is_sat_raw f sat_no) in
          match result1 with
          | Some f -> f
          | None ->
              omega_count := !omega_count + 1;
              (Omega.is_sat f sat_no)
      end
  | OM ->
      if (is_bag_constraint f) then
        begin
          (Mona.is_sat f sat_no);
        end
      else
        begin
          (Omega.is_sat f sat_no);
        end
  | OI ->
      if (is_bag_constraint f) then
        begin
          (Isabelle.is_sat f sat_no);
        end
      else
        begin
          (Omega.is_sat f sat_no);
        end
  | SetMONA -> Setmona.is_sat f
  | Redlog -> Redlog.is_sat f sat_no
  | RM ->
      if (is_bag_constraint f) then
        Mona.is_sat f sat_no
      else
        Redlog.is_sat f sat_no

let tp_is_sat_no_cache_debug f sat_no =
  Util.ho_debug_2 "tp_is_sat_no_cache " Cprinter.string_of_pure_formula (fun x-> x) string_of_bool tp_is_sat_no_cache f sat_no
        
        
let prune_sat_cache  = Hashtbl.create 2000 ;;




let tp_is_sat (f: CP.formula) (sat_no: string) =
  if !Globals.no_cache_formula then
    tp_is_sat_no_cache f sat_no
  else
    (*let _ = Util.push_time "cache overhead" in*)
    let sf = simplify_var_name f in
    let fstring = Cprinter.string_of_pure_formula sf in
    (*let _ = Util.pop_time "cache overhead" in*)
    let res =
      try
        Hashtbl.find !sat_cache fstring
      with Not_found ->
        let r = tp_is_sat_no_cache(*_debug*) f sat_no in
        (*let _ = Util.push_time "cache overhead" in*)
        let _ = Hashtbl.add !sat_cache fstring r in
        (*let _ = Util.pop_time "cache overhead" in*)
        r
    in res


let tp_is_sat (f: CP.formula) (sat_no: string) do_cache =
  if !Globals.enable_prune_cache (*&& do_cache*) then
    (
    Util.inc_counter "sat_cache_count";
    let s = (!print_pure f) in
    try 
      let r = Hashtbl.find prune_sat_cache s in
      (*print_string ("sat hits: "^s^"\n");*)
      r
    with Not_found -> 
        let r = tp_is_sat f sat_no in
        (Hashtbl.add prune_sat_cache s r ;
        Util.inc_counter "sat_proof_count";
        r))
  else  
    tp_is_sat f sat_no
;;
    
let simplify_omega (f:CP.formula): CP.formula = 
   if is_bag_constraint f then f
    else Omega.simplify f   
            
let simplify (f : CP.formula) : CP.formula =
  if !external_prover then 
    match Netprover.call_prover (Simplify f) with
        Some res -> res
      | None -> f
  else
    (Util.push_time "simplify";
    try
	  let r = match !tp with
        | Isabelle -> Isabelle.simplify f
        | Coq -> Coq.simplify f
        | Mona -> Mona.simplify f
        | OM ->
              if (is_bag_constraint f) then
                (Mona.simplify f)
              else (Omega.simplify f)
        | OI ->
              if (is_bag_constraint f) then
                (Isabelle.simplify f)
              else (Omega.simplify f)
        | SetMONA -> Mona.simplify f
        | CM ->
              if is_bag_constraint f then Mona.simplify f
              else Omega.simplify f
        | Redlog -> Redlog.simplify f
        | RM -> 
              if is_bag_constraint f then
                Mona.simplify f
              else
                Redlog.simplify f
        | _ -> Omega.simplify f in
      Util.pop_time "simplify";
      r
    with | _ -> f)

let hull (f : CP.formula) : CP.formula = match !tp with
  | Isabelle -> Isabelle.hull f
  | Coq -> Coq.hull f
  | Mona -> Mona.hull f
  | OM ->
	  if (is_bag_constraint f) then
		(Mona.hull f)
	  else (Omega.hull f)
  | OI ->
	  if (is_bag_constraint f) then
		(Isabelle.hull f)
	  else (Omega.hull f)
  | SetMONA -> Mona.hull f
  | CM ->
	  if is_bag_constraint f then Mona.hull f
	  else Omega.hull f
  | Redlog -> Redlog.hull f
  | RM ->
      if is_bag_constraint f then
        Mona.hull f
      else
        Redlog.hull f
  | _ ->
	  (*
		if (is_bag_constraint f) then
		failwith ("[Tpdispatcher.ml]: The specification contains bag constraints which cannot be handled by Omega\n")
	  else
	  *)
	  (Omega.hull f)


let pairwisecheck (f : CP.formula) : CP.formula = match !tp with
  | Isabelle -> Isabelle.pairwisecheck f
  | Coq -> Coq.pairwisecheck f
  | Mona -> Mona.pairwisecheck f
  | OM ->
	  if (is_bag_constraint f) then
		(Mona.pairwisecheck f)
	  else (Omega.pairwisecheck f)
  | OI ->
	  if (is_bag_constraint f) then
		(Isabelle.pairwisecheck f)
	  else (Omega.pairwisecheck f)
  | SetMONA -> Mona.pairwisecheck f
  | CM ->
	  if is_bag_constraint f then Mona.pairwisecheck f
	  else Omega.pairwisecheck f
  | Redlog -> Redlog.pairwisecheck f
  | RM ->
      if is_bag_constraint f then Mona.pairwisecheck f
      else Redlog.pairwisecheck f
  | _ ->
	  (*
	  if (is_bag_constraint f) then
		failwith ("[Tpdispatcher.ml]: The specification contains bag constraints which cannot be handled by Omega\n")
	  else
	  *)
	  (Omega.pairwisecheck f)

(*
let rec imply (ante : CP.formula) (conseq : CP.formula) : bool =
  let tmp1 = CP.break_implication ante conseq in
	if (List.length tmp1) <= 1 then
	  imply1 ante conseq
	else
	  let _ = print_string ("splitting...") in
	  let res = List.for_all (fun (a, c) -> imply1 a c) tmp1 in
		res
*)

let rec split_conjunctions = function
  | CP.And (x, y, _) -> (split_conjunctions x) @ (split_conjunctions y)
  | z -> [z]
;;

let rec split_disjunctions = function
  | CP.Or (x, y, _,_) -> (split_disjunctions x) @ (split_disjunctions y)
  | z -> [z]
;;

let called_prover = ref ""

let tp_imply_no_cache ante conseq imp_no timeout =
  (* let _ = print_string ("XXX"^(Cprinter.string_of_pure_formula ante)^"//"
                  ^(Cprinter.string_of_pure_formula conseq)^"\n") in
   *)
  match !tp with
  | OmegaCalc -> (Omega.imply ante conseq (imp_no^"XX") timeout)
  | CvcLite -> Cvclite.imply ante conseq
  | Cvc3 -> Cvc3.imply ante conseq
  | Z3 -> Smtsolver.imply ante conseq
  | Isabelle -> Isabelle.imply ante conseq imp_no
  | Coq -> Coq.imply ante conseq
  | Mona -> Mona.imply timeout ante conseq imp_no 
  | CO -> 
      begin
        let result1 = Cvclite.imply_raw ante conseq in
        match result1 with
        | Some f -> f
        | None -> (* CVC Lite is not sure is this case, try Omega *)
            omega_count := !omega_count + 1;
            Omega.imply ante conseq imp_no timeout
      end
  | CM -> 
      begin
        if (is_bag_constraint ante) || (is_bag_constraint conseq) then
          Mona.imply timeout ante conseq imp_no
        else
          let result1 = Cvclite.imply_raw ante conseq in
          match result1 with
          | Some f -> f
          | None -> (* CVC Lite is not sure is this case, try Omega *)
              omega_count := !omega_count + 1;
              Omega.imply ante conseq imp_no timeout
      end
  | OM ->
	  if (is_bag_constraint ante) || (is_bag_constraint conseq) then
		(called_prover :="mona " ; Mona.imply timeout ante conseq imp_no)
	  else
		(called_prover :="omega " ; Omega.imply ante conseq imp_no timeout)
  | OI ->
      if (is_bag_constraint ante) || (is_bag_constraint conseq) then
        (Isabelle.imply ante conseq imp_no)
      else
        (Omega.imply ante conseq imp_no timeout)
  | SetMONA -> Setmona.imply ante conseq 
  | Redlog -> Redlog.imply ante conseq imp_no 
  | RM -> 
      if (is_bag_constraint ante) || (is_bag_constraint conseq) then
        Mona.imply timeout ante conseq imp_no
      else
        Redlog.imply ante conseq imp_no
;;
 

let imply_cache  = Hashtbl.create 2000 ;;
let impl_conseq_cache  = Hashtbl.create 2000 ;;

let add_conseq_to_cache s = 
  try
    let _ = Hashtbl.find impl_conseq_cache s in ()
  with
    | Not_found -> 
          (Util.inc_counter "impl_conseq_count";
          Hashtbl.add impl_conseq_cache s ()
          )
          
let tp_imply ante conseq imp_no timeout =
  if !Globals.no_cache_formula then
    tp_imply_no_cache ante conseq imp_no timeout
  else
    (*let _ = Util.push_time "cache overhead" in*)
    let f = CP.mkOr conseq (CP.mkNot ante None no_pos) None no_pos in
    let sf = simplify_var_name f in
    let fstring = Cprinter.string_of_pure_formula sf in
    (*let _ = Util.pop_time "cache overhead" in*)
    let res = 
      try
        Hashtbl.find !impl_cache fstring
      with Not_found ->
        let r = tp_imply_no_cache ante conseq imp_no timeout in
        (*let _ = Util.push_time "cache overhead" in*)
        let _ = Hashtbl.add !impl_cache fstring r in
        (*let _ = Util.pop_time "cache overhead" in*)
        r
    in res

    
let tp_imply ante conseq imp_no timeout do_cache =
  if !Globals.enable_prune_cache (*&& do_cache*) then
    (
    Util.inc_counter "impl_cache_count";
    add_conseq_to_cache (!print_pure conseq) ;
    let s_rhs = !print_pure conseq in
    let s = (!print_pure ante)^"/"^ s_rhs in
    try 
      let r = Hashtbl.find imply_cache s in
      (* print_string ("hit rhs: "^s_rhs^"\n");*)
      r
      with Not_found -> 
        let r = tp_imply ante conseq imp_no timeout in
        (Hashtbl.add imply_cache s r ;
         (*print_string ("s rhs: "^s_rhs^"\n");*)
         Util.inc_counter "impl_proof_count";
        r))
  else  
    tp_imply ante conseq imp_no timeout
;;

let tp_imply_debug ante conseq imp_no timeout do_cache =
 Util.ho_debug_5 "tp_imply " 
  Cprinter.string_of_pure_formula 
  Cprinter.string_of_pure_formula
 (fun c-> c) (fun _ -> "?") string_of_bool 
 string_of_bool (fun x-> true)
 tp_imply ante conseq imp_no timeout do_cache

(* renames all quantified variables *)
let rec requant = function
  | CP.And (f, g, l) -> CP.And (requant f, requant g, l)
  | CP.Or (f, g, lbl, l) -> CP.Or (requant f, requant g, lbl, l)
  | CP.Not (f, lbl, l) -> CP.Not (requant f, lbl, l)
  | CP.Forall (v, f, lbl, l) ->
      let nv = CP.fresh_spec_var v in
      CP.Forall (nv, (CP.subst [v, nv] (requant f)), lbl, l)
  | CP.Exists (v, f, lbl, l) ->
      let nv = CP.fresh_spec_var v in
      CP.Exists (nv, (CP.subst [v, nv] (requant f)), lbl, l)
  | x -> x
;;

let rewrite_in_list list formula =
  match formula with
  | CP.BForm (CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _),_) ->
      List.map (fun x -> if x <> formula then CP.subst [v1, v2] x else x) list
  | CP.BForm (CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _),_) ->
      List.map (fun x -> if x <> formula then CP.subst_term [v1, term] x else x) list
  | x -> list
;;

let rec rewrite_in_and_tree rid formula rform =
  match formula with
  | CP.And (x, y, l) ->
      let (x, fx) = rewrite_in_and_tree rid x rform in
      let (y, fy) = rewrite_in_and_tree rid y rform in
      (CP.And (x, y, l), (fun e -> fx (fy e)))
  | x ->
      let subst_fun =
        match rform with
        | CP.BForm (CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _),_) -> CP.subst [v1, v2]
        | CP.BForm (CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _),_) -> CP.subst_term [v1, term]
        | CP.BForm (CP.Eq ((CP.IConst(i, _) as term), CP.Var (v1, _), _),_) -> CP.subst_term [v1, term]
        | _ -> fun x -> x
      in
      if ((not rid) && x = rform) then (x, subst_fun) else (subst_fun x, subst_fun)
;;

let is_irrelevant = function
  | CP.BForm (CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _),_) -> v1 = v2
  | CP.BForm (CP.Eq (CP.IConst(i1, _), CP.IConst(i2, _), _),_) -> i1 = i2
  | _ -> false
;;

let rec get_rid_of_eq = function
  | CP.And (x, y, l) -> 
      if is_irrelevant x then (get_rid_of_eq y) else
      if is_irrelevant y then (get_rid_of_eq x) else
      CP.And (get_rid_of_eq x, get_rid_of_eq y, l)
  | z -> z
;;

let rec fold_with_subst fold_fun current = function
  | [] -> current
  | h :: t ->
      let current, subst_fun = fold_fun current h in
      fold_with_subst fold_fun current (List.map subst_fun t)
;;

(* TODO goes in just once *)
let rec simpl_in_quant formula negated rid =
  match negated with
  | true ->
      begin match formula with
      | CP.Not (f, lbl, l) -> CP.Not (simpl_in_quant f false rid, lbl, l)
      | CP.Forall (v, f, lbl, l) -> CP.Forall (v, simpl_in_quant f true rid, lbl, l)
      | CP.Exists (v, f, lbl, l) -> CP.Exists (v, simpl_in_quant f true rid, lbl, l)
      | CP.Or (f, g, lbl, l) -> CP.Or (simpl_in_quant f false false, simpl_in_quant g false false, lbl, l)
      | CP.And (_, _, _) ->
          let subfs = split_conjunctions formula in
          let nformula = fold_with_subst (rewrite_in_and_tree rid) formula subfs in
          let nformula = get_rid_of_eq nformula in
          nformula
      | x -> x
      end
  | false ->
      begin match formula with
      | CP.Not (f, lbl, l) -> CP.Not (simpl_in_quant f true true, lbl, l)
      | CP.Forall (v, f, lbl, l) -> CP.Forall (v, simpl_in_quant f false rid, lbl, l)
      | CP.Exists (v, f, lbl, l) -> CP.Exists (v, simpl_in_quant f false rid, lbl, l)
      | CP.And (f, g, l) -> CP.And (simpl_in_quant f true false, simpl_in_quant g true false, l)
      | x -> x
      end
;;

let simpl_pair rid (ante, conseq) =
  let l1 = CP.bag_vars_formula ante in
  let l1 = Util.remove_dups (l1 @ (CP.bag_vars_formula conseq)) in
  let antes = split_conjunctions ante in
  let fold_fun l_f_vars (ante, conseq)  = function
    | CP.BForm (CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _),_) ->
        ((CP.subst [v1, v2] ante, CP.subst [v1, v2] conseq), (CP.subst [v1, v2]))
    | CP.BForm (CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _),_)
    | CP.BForm (CP.Eq ((CP.IConst(i, _) as term), CP.Var (v1, _), _),_) ->
		if (List.mem v1 l1) then ((ante, conseq), fun x -> x)
		 else ((CP.subst_term [v1, term] ante, CP.subst_term [v1, term] conseq), (CP.subst_term [v1, term]))
    | _ -> ((ante, conseq), fun x -> x)
  in
  let (ante1, conseq) = fold_with_subst (fold_fun l1) (ante, conseq) antes in
  let ante1 = get_rid_of_eq ante1 in
  let ante2 = simpl_in_quant ante1 true rid in
  let ante3 = simpl_in_quant ante2 true rid in
  (ante3, conseq)
;;

let is_sat (f : CP.formula) (sat_no : string) do_cache: bool =
  proof_no := !proof_no+1 ;
  let sat_no = (string_of_int !proof_no) in
  Debug.devel_pprint ("SAT #" ^ sat_no) no_pos;
  
  let f = elim_exists f in
  if (CP.isConstTrue f) then true 
  else if (CP.isConstFalse f) then false
  else  let (f, _) = simpl_pair true (f, CP.mkFalse no_pos) in
    tp_is_sat f sat_no do_cache
;;

let imply_timeout (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout do_cache
	: bool*(formula_label option * formula_label option )list * (formula_label option) = (*result+successfull matches+ possible fail*)
  proof_no := !proof_no + 1 ; 
  let imp_no = (string_of_int !proof_no) in
  Debug.devel_pprint ("IMP #" ^ imp_no) no_pos;  
  if !external_prover then 
    match Netprover.call_prover (Imply (ante0,conseq0)) with
      Some res -> (res,[],None)       
      | None -> (false,[],None)
  else begin 
	(*let _ = print_string ("Imply: => " ^(Cprinter.string_of_pure_formula ante0)^"\n==> "^(Cprinter.string_of_pure_formula conseq0)) in*)
	let conseq = if CP.should_simplify conseq0 then simplify conseq0 else conseq0 in
	if CP.isConstTrue conseq0 then (true, [],None)
	else
let ante = if CP.should_simplify ante0 then simplify ante0 else ante0 in
		if CP.isConstFalse ante0 || CP.isConstFalse ante then (true,[],None)
		else
			let ante = elim_exists ante in
			let conseq = elim_exists conseq in
			let split_conseq = split_conjunctions conseq in
			let pairs = List.map (fun cons -> 
        let (ante,cons) = simpl_pair false (requant ante, requant cons) in 
        let ante = CP.remove_dup_constraints ante in
        filter ante cons) split_conseq in
			let pairs_length = List.length pairs in
			let imp_sub_no = ref 0 in
			let fold_fun (res1,res2,res3) (ante, conseq) =
				(incr imp_sub_no;
				if res1 then 
					let imp_no = 
						if pairs_length > 1 then (imp_no ^ "." ^ string_of_int (!imp_sub_no))
						else imp_no in
					let res1 =
						if (not (CP.is_formula_arith ante))&& (CP.is_formula_arith conseq) then 
							let res1 = tp_imply(*_debug*) (CP.drop_bag_formula ante) conseq imp_no timeout do_cache in
							if res1 then res1
							else tp_imply(*_debug*) ante conseq imp_no timeout do_cache
						else tp_imply(*_debug*) ante conseq imp_no timeout do_cache in
					let l1 = CP.get_pure_label ante in
					let l2 = CP.get_pure_label conseq in
					if res1 then (res1,(l1,l2)::res2,None)
					else (res1,res2,l2)
				else (res1,res2,res3) )
			in
			List.fold_left fold_fun (true,[],None) pairs
  end
;;

let imply_timeout ante0 conseq0 imp_no timeout do_cache =
  let s = "imply" in
  let _ = Util.push_time s in
  let (res1,res2,res3) = imply_timeout ante0 conseq0 imp_no timeout do_cache in
  let _ = Util.pop_time s in
  if res1  then Util.inc_counter "true_imply_count" else Util.inc_counter "false_imply_count" ; 
  (res1,res2,res3)
;;

let memo_imply_timeout ante0 conseq0 imp_no timeout = 
  let _ = Util.push_time "memo_imply" in
  let r = List.fold_left (fun (r1,r2,r3) c->
    if not r1 then (r1,r2,r3)
    else 
      let l = List.filter (fun d-> (List.length (Util.intersect_fct CP.eq_spec_var c.MCP.memo_group_fv d.MCP.memo_group_fv))>0) ante0 in
      let ant = MCP.fold_mem_lst_m (CP.mkTrue no_pos) true true l in
      let con = MCP.fold_mem_lst_m (CP.mkTrue no_pos) true false [c] in
      let r1',r2',r3' = imply_timeout ant con imp_no timeout false in 
      (r1',r2@r2',r3')) (true, [], None) conseq0 in
  let _ = Util.pop_time "memo_imply" in
  r
;;

let mix_imply_timeout ante0 conseq0 imp_no timeout = match ante0,conseq0 with
  | MCP.MemoF a, MCP.MemoF c -> memo_imply_timeout a c imp_no timeout
  | MCP.OnePF a, MCP.OnePF c -> imply_timeout a c imp_no timeout false
  | _ -> report_error no_pos ("mix_imply_timeout: mismatched mix formulas ")

let imply ante0 conseq0 imp_no do_cache = imply_timeout ante0 conseq0 imp_no 0. do_cache
;;

let memo_imply ante0 conseq0 imp_no = memo_imply_timeout ante0 conseq0 imp_no 0.
;;

let mix_imply ante0 conseq0 imp_no = mix_imply_timeout ante0 conseq0 imp_no 0.
;;


let is_sat f sat_no do_cache =
  if !external_prover then 
      match Netprover.call_prover (Sat f) with
      Some res -> res       
      | None -> false
  else  begin   

	let _ = Util.push_time "is_sat" in
  let res = is_sat f sat_no do_cache in
	let _ = Util.pop_time "is_sat" in  
	res end
;;

let sat_no = ref 1
;;
let incr_sat_no () = 
 sat_no := !sat_no +1 
;;

let is_sat_sub_no_c (f : CP.formula) sat_subno do_cache : bool = 
  let sat = is_sat f ((string_of_int !sat_no) ^ "." ^ (string_of_int !sat_subno)) do_cache in
  Debug.devel_pprint ("SAT #" ^ (string_of_int !sat_no) ^ "." ^ (string_of_int !sat_subno)) no_pos;
  sat_subno := !sat_subno+1;
  sat
;;

let is_sat_sub_no (f : CP.formula) sat_subno : bool =  is_sat_sub_no_c f sat_subno false;;

let is_sat_sub_no_debug (f : CP.formula) sat_subno : bool =  
  Util.ho_debug_2 "is_sat_sub_no " (Cprinter.string_of_pure_formula) (fun x-> string_of_int !x)
    (string_of_bool ) is_sat_sub_no f sat_subno;;

let is_sat_memo_sub_no (f : MCP.memo_pure) sat_subno with_dupl with_inv : bool = 
  let f_lst = MCP.fold_mem_lst_to_lst f with_dupl with_inv true in
  not (List.fold_left (fun a c-> if a then a else not (is_sat_sub_no c sat_subno)) false f_lst)
;;

let is_sat_mix_sub_no (f : MCP.mix_formula) sat_subno with_dupl with_inv : bool = match f with
  | MCP.MemoF f -> is_sat_memo_sub_no f sat_subno with_dupl with_inv
  | MCP.OnePF f -> is_sat_sub_no f sat_subno

let is_sat_msg_no_no prof_lbl (f:CP.formula) do_cache :bool = 
  let sat_subno = ref 0 in
  let _ = Util.push_time prof_lbl in
  let sat = is_sat_sub_no_c f sat_subno do_cache in
  let _ = Util.pop_time prof_lbl in
  sat
  
let imply_sub_no ante0 conseq0 imp_no do_cache=
  Debug.devel_pprint ("IMP #" ^ imp_no ^ "\n") no_pos;
  (* imp_no := !imp_no+1;*)
  imply ante0 conseq0 imp_no do_cache

let imply_msg_no_no ante0 conseq0 imp_no prof_lbl do_cache =
  let _ = Util.push_time prof_lbl in  
  let r = imply_sub_no ante0 conseq0 imp_no do_cache in
  let _ = Util.pop_time prof_lbl in
  r
let imply_msg_no_no_debug ante0 conseq0 imp_no prof_lbl do_cache =
Util.ho_debug_5 "imply_msg_no_no " 
  Cprinter.string_of_pure_formula 
  Cprinter.string_of_pure_formula
 (fun c-> c) (fun _ -> "?") string_of_bool 
 (fun (x,_,_)-> string_of_bool x) (fun x-> true)
 imply_msg_no_no ante0 conseq0 imp_no prof_lbl do_cache
  
let print_stats () =
  print_string ("\nTP statistics:\n");
  print_string ("omega_count = " ^ (string_of_int !omega_count) ^ "\n")

let start_prover () =
  match !tp with
  | Coq -> Coq.start_prover ()
  | Redlog | RM -> 
     begin
      Redlog.start_red ();
	  Omega.start_omega ();
	 end
  | _ -> Omega.start_omega ()
  
let stop_prover () =
  match !tp with
  | Coq -> Coq.stop_prover ()
  | Redlog | RM -> 
    begin
     Redlog.stop_red ();
	 Omega.stop_omega ();
	end
  | _ -> Omega.stop_omega ();

