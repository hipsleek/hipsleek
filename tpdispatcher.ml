(*

  Choose with theorem prover to prove formula
*)

open Globals
open Gen.Basic
module CP = Cpure
module MCP = Mcpure

type tp_type =
  | OmegaCalc
  | CvcLite
  | Cvc3
  | CO (* CVC3 then Omega combination *)
  | Isabelle
  | Mona
  | MonaH
  | OM
  | OI
  | SetMONA
  | CM (* CVC3 then MONA *)
  | Coq
  | Z3
  | Redlog
  | RM (* Redlog and Mona *)
  | ZM (* Z3 and Mona *)

let tp = ref OmegaCalc
let proof_no = ref 0
let provers_process = ref None

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
    (* let _ = print_string ("\n Tpdispatcher: start_prover_process \n") in *)
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
          let in_fds, _, _ = Gen.Basic.restart  (Unix.select [wait_fd] [] []) time_left in
          (* let in_fds, _, _ = Unix.select [wait_fd] [] [] time_left in *)
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

(* ##################################################################### *)

(* class used for keeping prover's functions needed for the incremental proving*)
class incremMethods : [CP.formula] Globals.incremMethodsType = object

  (*keeps track of the number of saved states of the current process*)
  val push_no = ref 0
    (*variable used to archives all the assumptions send to the current process *)
  val process_context = ref []
    (*variable used to archive all the declared variables in the current process context *)
  val declarations = ref [] (* (stack_no * var_name * var_type) list*)
    (* prover process *)
  val process = ref None

  (*creates a new proving process *)
  method start_p () : Globals.prover_process_t =
    let proc = 
      match !tp with
      | Cvc3 -> Cvc3.start()
      | _ -> Cvc3.start() (* to be completed for the rest of provers that support incremental proving *) 
    in 
    process := Some proc;
    proc

  (*stops the proving process*)
  method stop_p (process: Globals.prover_process_t): unit =
    match !tp with
      | Cvc3 -> Cvc3.stop process
      | _ -> () (* to be completed for the rest of provers that support incremental proving *)

  (*saves the state of the process and its context *)
  method push (process: Globals.prover_process_t): unit = 
    push_no := !push_no + 1;
      match !tp with
        | Cvc3 -> Cvc3.cvc3_push process
        | _ -> () (* to be completed for the rest of provers that support incremental proving *)

  (*returns the process to the state it was before the push call *)
  method pop (process: Globals.prover_process_t): unit = 
    match !tp with
      | Cvc3 -> Cvc3.cvc3_pop process
      | _ -> () (* to be completed for the rest of provers that support incremental proving *)

  (*returns the process to the state it was before the push call on stack n *)
  method popto (process: Globals.prover_process_t) (n: int): unit = 
    let n = 
      if ( n > !push_no) then begin
        Debug.devel_pprint ("\nCannot pop to " ^ (string_of_int n) ^ ": no such stack. Will pop to stack no. " ^ (string_of_int !push_no)) no_pos;
        !push_no 
      end
      else n in
    match !tp with
      | Cvc3 -> Cvc3.cvc3_popto process n
      | _ -> () (* to be completed for the rest of provers that support incremental proving *)

  method imply (process: (Globals.prover_process_t option * bool) option) (ante: CP.formula) (conseq: CP.formula) (imp_no: string): bool = true
    (* let _ = match proceess with  *)
    (*   | Some (Some proc, send_ante) -> if (send_ante) then  *)
    (*       else *)
    (*      imply process ante conseq imp_no *)

    (*adds active assumptions to the current process*)
    (* method private add_to_context assertion: unit = *)
    (*     process_context := [assertion]@(!process_context) *)

  method set_process (proc: Globals.prover_process_t) =
    process := Some proc

  method get_process () : Globals.prover_process_t option =
    !process 

end

let incremMethodsO = ref (new incremMethods)


(* ##################################################################### *)

let rec check_prover_existence prover_cmd_str =
  match prover_cmd_str with
    |[] -> ()
    | prover::rest -> 
        let exit_code = Sys.command ("which "^prover) in
        if exit_code > 0 then
          let _ = print_string ("Command for starting the prover (" ^ prover ^ ") not found\n") in
          exit 0
        else check_prover_existence rest

let set_tp tp_str =
  prover_arg := tp_str;  
  let prover_str = ref [] in
  if tp_str = "omega" then
	(tp := OmegaCalc; prover_str := "oc"::!prover_str;)
  else if tp_str = "cvcl" then 
	(tp := CvcLite; prover_str := "cvcl"::!prover_str;)
  else if tp_str = "cvc3" then 
	(tp := Cvc3; prover_str := "cvc3"::!prover_str;)
  else if tp_str = "co" then
	(tp := CO; prover_str := "cvc3"::!prover_str; 
     prover_str := "oc"::!prover_str;)
  else if tp_str = "isabelle" then
	(tp := Isabelle; prover_str := "isabelle-process"::!prover_str;)
  else if tp_str = "mona" then
	(tp := Mona; prover_str := "mona"::!prover_str;)
  else if tp_str = "monah" then
	(tp := MonaH; prover_str := "mona"::!prover_str;)
  else if tp_str = "om" then
	(tp := OM; prover_str := "oc"::!prover_str;
     prover_str := "mona"::!prover_str;)
  else if tp_str = "oi" then
	(tp := OI; prover_str := "oc"::!prover_str;
     prover_str := "isabelle-process"::!prover_str;)
  else if tp_str = "set" then
    (tp := SetMONA; prover_str := "mona"::!prover_str;)
  else if tp_str = "cm" then
	(tp := CM; prover_str := "cvc3"::!prover_str;
     prover_str := "mona"::!prover_str;)
  else if tp_str = "coq" then
	(tp := Coq; prover_str := "coqtop"::!prover_str;)
  else if tp_str = "z3" then 
	(tp := Z3; prover_str := "z3"::!prover_str;)
  else if tp_str = "redlog" then
    (tp := Redlog; prover_str := "redcsl"::!prover_str;)
  else if tp_str = "rm" then
    tp := RM
  else if tp_str = "zm" then
    tp := ZM
  else if tp_str = "prm" then
    (Redlog.is_presburger := true; tp := RM)
  else
	();
  check_prover_existence !prover_str

let string_of_tp tp = match tp with
  | OmegaCalc -> "omega"
  | CvcLite -> "cvcl"
  | Cvc3 -> "cvc3"
  | CO -> "co"
  | Isabelle -> "isabelle"
  | Mona -> "mona"
  | MonaH -> "monah"
  | OM -> "om"
  | OI -> "oi"
  | SetMONA -> "set"
  | CM -> "cm"
  | Coq -> "coq"
  | Z3 -> "z3"
  | Redlog -> "redlog"
  | RM -> "rm"
  | ZM -> "zm"

let name_of_tp tp = match tp with
  | OmegaCalc -> "Omega Calculator"
  | CvcLite -> "CVC Lite"
  | Cvc3 -> "CVC3"
  | CO -> "CVC Lite and Omega"
  | Isabelle -> "Isabelle"
  | Mona -> "Mona"
  | MonaH -> "MonaH"
  | OM -> "Omega and Mona"
  | OI -> "Omega and Isabelle"
  | SetMONA -> "Set Mona"
  | CM -> "CVC Lite and Mona"
  | Coq -> "Coq"
  | Z3 -> "Z3"
  | Redlog -> "Redlog"
  | RM -> "Redlog and Mona"
  | ZM -> "Z3 and Mona"

let log_file_of_tp tp = match tp with
  | OmegaCalc -> "allinput.oc"
  | Cvc3 -> "allinput.cvc3"
  | Isabelle -> "allinput.thy"
  | Mona -> "allinput.mona"
  | Coq -> "allinput.v"
  | Redlog -> "allinput.rl"
  | Z3 -> "allinput.z3"
  | _ -> ""

let get_current_tp_name () = name_of_tp !tp

let omega_count = ref 0

(* Method checking whether a formula contains bag constraints *)

let is_bag_b_constraint (pf,_) = match pf with
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
let rec is_list_exp e = match e with
    | CP.List _
    | CP.ListCons _
    | CP.ListHead _
    | CP.ListTail _
    | CP.ListLength _
    | CP.ListAppend _
    | CP.ListReverse _ 
        -> Some true
	| CP.Add (e1,e2,_)
	| CP.Subtract (e1,e2,_)
	| CP.Mult (e1,e2,_)
	| CP.Div (e1,e2,_)
	| CP.Max (e1,e2,_)
	| CP.Min (e1,e2,_)
	| CP.BagDiff (e1,e2,_)
		-> (match (is_list_exp e1) with
						| Some true -> Some true
						| _ -> is_list_exp e2)
	| CP.Bag (el,_)
	| CP.BagUnion (el,_)
	| CP.BagIntersect (el,_)
		-> (List.fold_left (fun res exp -> match res with
											| Some true -> Some true
											| _ -> is_list_exp exp) (Some false) el)
    | _ -> Some false
	  
(*let f_e e = Gen.Debug.no_1 "f_e" (Cprinter.string_of_formula_exp) (fun s -> match s with
	| Some ss -> string_of_bool ss
	| _ -> "") f_e_1 e
*)	

let is_list_b_formula (pf,_) = match pf with
    | CP.BConst _ 
    | CP.BVar _
	| CP.BagMin _ 
    | CP.BagMax _
		-> Some false    
    | CP.Lt (e1,e2,_) 
    | CP.Lte (e1,e2,_) 
    | CP.Gt (e1,e2,_)
    | CP.Gte (e1,e2,_)
	| CP.Eq (e1,e2,_)
	| CP.Neq (e1,e2,_)
	| CP.BagSub (e1,e2,_)
		-> (match (is_list_exp e1) with
						| Some true -> Some true
						| _ -> is_list_exp e2)
    | CP.EqMax (e1,e2,e3,_)
    | CP.EqMin (e1,e2,e3,_)
		-> (match (is_list_exp e1) with
						| Some true -> Some true
						| _ -> (match (is_list_exp e2) with
											| Some true -> Some true
											| _ -> is_list_exp e3))
    | CP.BagIn (_,e,_) 
    | CP.BagNotIn (_,e,_)
		-> is_list_exp e
    | CP.ListIn _ 
    | CP.ListNotIn _
    | CP.ListAllN _ 
    | CP.ListPerm _
        -> Some true
    | _ -> None
 
let is_list_constraint (e: CP.formula) : bool =
 
  let or_list = List.fold_left (||) false in
  CP.fold_formula e (nonef, is_list_b_formula, is_list_exp) or_list

let is_list_constraint (e: CP.formula) : bool =
  (*Gen.Debug.no_1_opt "is_list_constraint" Cprinter.string_of_pure_formula string_of_bool (fun r -> not(r)) is_list_constraint e*)
  Gen.Debug.no_1 "is_list_constraint" Cprinter.string_of_pure_formula string_of_bool is_list_constraint e
  
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

let filter_orig (ante : CP.formula) (conseq : CP.formula) : (CP.formula list * CP.formula) =
 (* let _ = print_string ("\naTpdispatcher.ml: filter") in *)
  if !filtering_flag (*&& (not !allow_pred_spec)*) then
    ([CP.filter_ante ante conseq], conseq)
	(* let fvar = CP.fv conseq in *)
	(* let new_ante = CP.filter_var ante fvar in *)
	(*   (new_ante, conseq) *)
  else
    (* let _ = print_string ("\naTpdispatcher.ml: no filter") in *)
	([ante], conseq)

let filter_slicing (ante : CP.formula) (cons : CP.formula) : (CP.formula list * CP.formula) =
  let overlap (nlv1, lv1) (nlv2, lv2) =
	if (nlv1 = [] && nlv2 = []) then
	  (Gen.BList.list_equiv_eq CP.eq_spec_var lv1 lv2)
	else
	  (Gen.BList.overlap_eq CP.eq_spec_var nlv1 nlv2) && (Gen.BList.list_equiv_eq CP.eq_spec_var lv1 lv2)
  in
  
  let rec group_conj l = match l with
    | [] -> (false,[]) 
    | ((f_nlv, f_lv), fs)::t ->  
      let b,l = group_conj t in
      let l1, l2 = List.partition (fun (cfv, _) -> overlap (f_nlv, f_lv) cfv) l in
      if l1==[] then (b,((f_nlv, f_lv), fs)::l) 
      else 
        let l_fv, nfs = List.split l1 in
		let l_nlv, l_lv = List.split l_fv in
        let nfs = CP.join_conjunctions (fs::nfs) in
        let n_nlv = CP.remove_dups_svl (List.concat (f_nlv::l_nlv)) in
		let n_lv = CP.remove_dups_svl (List.concat (f_lv::l_lv)) in
        (true,((n_nlv, n_lv), nfs)::l2)
  in
  
  let rec fix n_l = 
    let r1, r2 = group_conj n_l in
    if r1 then fix r2 else r2
  in    

  let split_sub_f f = 
    let conj_list = CP.split_conjunctions f in
    let n_l = List.map
	  (fun c -> (CP.fv_with_slicing_label c, c)) conj_list in
    snd (List.split (fix n_l))
  in

  let is_related f1 f2 =
	let (nlv1, lv1) = CP.fv_with_slicing_label f1 in
	let fv = CP.fv f2 in
	if (nlv1 == []) then
	  Gen.BList.overlap_eq CP.eq_spec_var fv lv1
	else
	  Gen.BList.overlap_eq CP.eq_spec_var fv nlv1
  in 

  let pick_rel_constraints cons ante =
	let fv = CP.fv cons in
	let rec exhaustive_collect_with_selection fv ante =
	  let (n_fv, n_ante1, r_ante) = List.fold_left (
		fun (afv, ac, rc) f ->
		  let f_ulv, f_lv = CP.fv_with_slicing_label f in
		  let cond_direct = Gen.BList.overlap_eq CP.eq_spec_var afv f_ulv in
		  let cond_link = (f_ulv = []) && (Gen.BList.subset_eq CP.eq_spec_var f_lv afv) in
		  if (cond_direct || cond_link) then
			(afv@(CP.fv f), ac@[f], rc)
		  else (afv, ac, rc@[f])
	  ) (fv, [], []) ante
	  in
	  if n_fv = fv then n_ante1
	  else
		let n_ante2 = exhaustive_collect_with_selection n_fv r_ante in
		n_ante1 @ n_ante2
	in
	exhaustive_collect_with_selection fv ante
  in

  let n_ante = CP.elim_exists_with_fresh_vars ante in

  let dnf_ante = CP.dnf_to_list n_ante in
    
  let l_ante = List.map (fun f ->
	let l_f = split_sub_f f in

	let _ = print_string ("imply_timeout: filter: l_f:\n" ^
    (List.fold_left (fun acc f -> acc ^ "+++++++++\n" ^ (Cprinter.string_of_pure_formula f) ^ "\n") "" l_f)) in
	
	(CP.join_conjunctions (pick_rel_constraints cons l_f))) dnf_ante
  in

  let _ = print_string ("imply_timeout: filter: l_ante:\n" ^
    (List.fold_left (fun acc ante -> acc ^ "\n++++++++++++++\n" ^ (Cprinter.string_of_pure_formula ante)) "" l_ante)
  ) in
  
  (l_ante, cons)
  
let filter (ante : CP.formula) (cons : CP.formula) : (CP.formula list * CP.formula) =
  if !do_slicing then
	filter_slicing ante cons
  else
	filter_orig ante cons
	  
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
  let f_bf vnames bf =
	let (pf,il) = bf in
	match pf with
    | CP.BVar (sv, l) -> Some ((CP.BVar (shorten_sv sv vnames, l)), il)
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
    | Cvc3 -> 
          begin
            match !provers_process with
              |Some proc -> Cvc3.is_sat_increm !provers_process f sat_no
              | _ -> Cvc3.is_sat f sat_no
                    (* Cvc3.is_sat f sat_no *)
          end
  | Z3 -> Smtsolver.is_sat f sat_no
  | Isabelle -> Isabelle.is_sat f sat_no
  | Coq -> (*Coq.is_sat f sat_no*)
      if (is_list_constraint f) then
        begin
          (Coq.is_sat f sat_no);
        end
      else
        begin
          (Omega.is_sat f sat_no);
        end
  | Mona | MonaH -> Mona.is_sat f sat_no
  | CO -> 
      begin
        let result1 = (Cvc3.is_sat_helper_separate_process f sat_no) in
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
          let result1 = (Cvc3.is_sat_helper_separate_process f sat_no) in
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
  | ZM ->
	  if (is_bag_constraint f) then
        Mona.is_sat f sat_no
      else
		Smtsolver.is_sat f sat_no

let tp_is_sat_no_cache f sat_no =
  Gen.Debug.ho_1 "tp_is_sat_no_cache" Cprinter.string_of_pure_formula string_of_bool 
    (fun f -> tp_is_sat_no_cache f sat_no) f
        
let prune_sat_cache  = Hashtbl.create 2000 ;;

let tp_is_sat (f: CP.formula) (sat_no: string) =
  if !Globals.no_cache_formula then
    tp_is_sat_no_cache f sat_no
  else
    (*let _ = Gen.Profiling.push_time "cache overhead" in*)
    let sf = simplify_var_name f in
    let fstring = Cprinter.string_of_pure_formula sf in
    (*let _ = Gen.Profiling.pop_time "cache overhead" in*)
    let res =
      try
        Hashtbl.find !sat_cache fstring
      with Not_found ->
        let r = tp_is_sat_no_cache(*_debug*) f sat_no in
        (*let _ = Gen.Profiling.push_time "cache overhead" in*)
        let _ = Hashtbl.add !sat_cache fstring r in
        (*let _ = Gen.Profiling.pop_time "cache overhead" in*)
        r
    in res

let tp_is_sat (f: CP.formula) (sat_no: string) do_cache =
  if !Globals.enable_prune_cache (*&& do_cache*) then
    (
    Gen.Profiling.inc_counter "sat_cache_count";
    let s = (!print_pure f) in
    try 
      let r = Hashtbl.find prune_sat_cache s in
      (*print_string ("sat hits: "^s^"\n");*)
      r
    with Not_found -> 
        let r = tp_is_sat_no_cache f sat_no in
        (Hashtbl.add prune_sat_cache s r ;
        Gen.Profiling.inc_counter "sat_proof_count";
        r))
  else  
    tp_is_sat f sat_no

let tp_is_sat f sat_no do_cache =
  Gen.Debug.ho_1 "tp_is_sat" Cprinter.string_of_pure_formula string_of_bool 
    (fun f -> tp_is_sat f sat_no do_cache) f

let simplify_omega (f:CP.formula): CP.formula = 
   if is_bag_constraint f then f
    else Omega.simplify f   
            
let simplify_omega f =
  Gen.Debug.no_1 "simplify_omega" Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula simplify_omega f

let simplify (f : CP.formula) : CP.formula =
  if !Globals.no_simpl then f else
  if !external_prover then 
    match Netprover.call_prover (Simplify f) with
        Some res -> res
      | None -> f
  else
    (Gen.Profiling.push_time "simplify";
    try
	  let r = match !tp with
        | Isabelle -> Isabelle.simplify f
        | Coq -> (* Coq.simplify f *)
              if (is_list_constraint f) then
                (Coq.simplify f)
              else (Omega.simplify f)
        | Mona | MonaH (* -> Mona.simplify f *) ->
            if (is_bag_constraint f) then
                (Mona.simplify f)
            else
              (* exist x, f0 ->  eexist x, x>0 /\ f0*)
              let f1 = CP.add_gte0_for_mona f in
              let f=(Omega.simplify f1) 
              in CP.arith_simplify 12 f
        | OM ->
              if (is_bag_constraint f) then
                (Mona.simplify f)
              else let f=(Omega.simplify f) 
              in CP.arith_simplify 12 f
        | OI ->
              if (is_bag_constraint f) then
                (Isabelle.simplify f)
              else (Omega.simplify f)
        | SetMONA -> Mona.simplify f
        | CM ->
              if is_bag_constraint f then Mona.simplify f
              else Omega.simplify f
        | Z3 -> Smtsolver.simplify f
        | Redlog -> Redlog.simplify f
        | RM -> 
              if is_bag_constraint f then
                Mona.simplify f
              else
                Redlog.simplify f
		| ZM -> 
              if is_bag_constraint f then
                Mona.simplify f
              else
                Smtsolver.simplify f
        | _ -> Omega.simplify f in
      Gen.Profiling.pop_time "simplify";
	  (*let _ = print_string ("\nsimplify: f after"^(Cprinter.string_of_pure_formula r)) in*)
	  (* To recreate <IL> relation after simplifying *)
	  (*let _ = print_string ("TP.simplify: ee formula:\n" ^ (Cprinter.string_of_pure_formula (Redlog.elim_exist_quantifier f))) in*)
	  if !Globals.do_slicing then
	    let rel_vars_lst =
		  let bfl = CP.break_formula f in
		  (*let bfl_no_il = List.filter
			(fun (_,il) -> match il with
			| None -> true
			| _ -> false) bfl in*)
		  (List.map (fun (svl,lkl,_) -> (svl,lkl)) (CP.group_related_vars bfl))
		in
		CP.set_il_formula_with_dept_list r rel_vars_lst
	  else r
    with | _ -> f)

let simplify (f : CP.formula) : CP.formula =
  Gen.Debug.ho_1 "simplify" Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula
	simplify f
	  
(* always simplify directly with the help of prover *)
let simplify_always (f:CP.formula): CP.formula = 
  let _ = Gen.Profiling.inc_counter ("stat_count_simpl") in
  simplify f 

(* let simplify f = *)
(*   Gen.Debug.no_1 "TP.simplify" Cprinter.string_of_pure_formula Cprinter.string_of_pure_formula (\* (fun x -> x) *\)simplify f *)

let simplify (f:CP.formula): CP.formula = 
  CP.elim_exists_with_simpl simplify f 
  (* if (CP.contains_exists f) then  *)
  (*   let f=CP.elim_exists f in  *)
  (*    simplify f else f *)

let simplify (f:CP.formula): CP.formula = 
  let pr = Cprinter.string_of_pure_formula in
  Gen.Debug.ho_1 "simplify" pr pr simplify f

(* let simplify (f:CP.formula): CP.formula =  *)
(*   (\* (if (2107 <= !Util.proc_ctr  && !Util.proc_ctr <= 2109) then  *\) *)
(*   (\*   begin *\) *)
(*   (\*     try *\) *)
(*   (\*       raise Omega.Timeout *\) *)
(*   (\*      with _ -> print_string ("BACKTRACE"^(Printexc.get_backtrace())) *\) *)
(*   (\*   end); *\) *)
(*   let pf = Cprinter.string_of_pure_formula in *)
(*   Gen.Debug.no_1 "TP.simplify0" pf pf simplify f *)

let simplify_a (s:int) (f:CP.formula): CP.formula = 
  (* (if (2107 <= !Util.proc_ctr  && !Util.proc_ctr <= 2109) then  *)
  (*   begin *)
  (*     try *)
  (*       raise Omega.Timeout *)
  (*      with _ -> print_string ("BACKTRACE"^(Printexc.get_backtrace())) *)
  (*   end); *)
  let pf = Cprinter.string_of_pure_formula in
  Gen.Debug.no_1 ("TP.simplify"^(string_of_int s)) pf pf simplify f

let hull (f : CP.formula) : CP.formula = match !tp with
  | Isabelle -> Isabelle.hull f
  | Coq -> (* Coq.hull f *)
      if (is_list_constraint f) then
		(Coq.hull f)
	  else (Omega.hull f)
  | Mona   -> Mona.hull f  
  | MonaH  (* -> Mona.hull f  *)
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
  | Z3 -> Smtsolver.hull f
  | Redlog -> Redlog.hull f
  | RM ->
      if is_bag_constraint f then
        Mona.hull f
      else
        Redlog.hull f
  | ZM ->
      if is_bag_constraint f then
        Mona.hull f
      else
        Smtsolver.hull f
  | _ ->
	  (*
		if (is_bag_constraint f) then
		failwith ("[Tpdispatcher.ml]: The specification contains bag constraints which cannot be handled by Omega\n")
	  else
	  *)
	  (Omega.hull f)

let hull (f : CP.formula) : CP.formula =
  let pr = Cprinter.string_of_pure_formula in
  Gen.Debug.ho_1 "hull" pr pr hull f

let pairwisecheck (f : CP.formula) : CP.formula = match !tp with
  | Isabelle -> Isabelle.pairwisecheck f
  | Coq -> (* Coq.pairwisecheck f *)
	  if (is_list_constraint f) then
		(Coq.pairwisecheck f)
	  else (Omega.pairwisecheck f)
  | Mona (* -> Mona.pairwisecheck f *)
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
  | Z3 -> Smtsolver.pairwisecheck f
  | Redlog -> Redlog.pairwisecheck f
  | RM ->
      if is_bag_constraint f then Mona.pairwisecheck f
      else Redlog.pairwisecheck f
  | ZM ->
      if is_bag_constraint f then Mona.pairwisecheck f
      else Smtsolver.pairwisecheck f
  | _ ->
	  (*
	  if (is_bag_constraint f) then
		failwith ("[Tpdispatcher.ml]: The specification contains bag constraints which cannot be handled by Omega\n")
	  else
	  *)
	  (Omega.pairwisecheck f)

let pairwisecheck (f : CP.formula) : CP.formula =
  let pr = Cprinter.string_of_pure_formula in
  Gen.Debug.ho_1 "pairwisecheck" pr pr pairwisecheck f

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
let print_implication = ref false 
  
let tp_imply_no_cache ante conseq imp_no timeout process =
  (* let _ = print_string ("XXX"^(Cprinter.string_of_pure_formula ante)^"//"
     ^(Cprinter.string_of_pure_formula conseq)^"\n") in
  *)
  (* let _ = print_string ("\nTpdispatcher.ml: tp_imply_no_cache") in *)
  
  let r = match !tp with
  | OmegaCalc -> (Omega.imply ante conseq (imp_no^"XX") timeout)
  | CvcLite -> Cvclite.imply ante conseq
    | Cvc3 -> begin
          match process with
            | Some (Some proc, _) -> Cvc3.imply_increm process ante conseq imp_no
            | _ -> Cvc3.imply_increm (Some (!provers_process,true)) ante conseq imp_no
            (* Cvc3.imply ante conseq imp_no *)
      end
  | Z3 -> Smtsolver.imply ante conseq
  | Isabelle -> Isabelle.imply ante conseq imp_no
  | Coq -> (* Coq.imply ante conseq *)
          if (is_list_constraint ante) || (is_list_constraint conseq) then
		    (called_prover :="coq " ; Coq.imply ante conseq)
	      else
		    (called_prover :="omega " ; Omega.imply ante conseq imp_no timeout)
  | Mona | MonaH -> Mona.imply ante conseq imp_no 
  | CO -> 
      begin
        let result1 = Cvc3.imply_helper_separate_process ante conseq imp_no in
        match result1 with
        | Some f -> f
        | None -> (* CVC Lite is not sure is this case, try Omega *)
            omega_count := !omega_count + 1;
            Omega.imply ante conseq imp_no timeout
      end
  | CM -> 
      begin
        if (is_bag_constraint ante) || (is_bag_constraint conseq) then
          Mona.imply ante conseq imp_no
        else
              let result1 = Cvc3.imply_helper_separate_process ante conseq imp_no in
          match result1 with
          | Some f -> f
          | None -> (* CVC Lite is not sure is this case, try Omega *)
              omega_count := !omega_count + 1;
              Omega.imply ante conseq imp_no timeout
      end
  | OM ->
	  if (is_bag_constraint ante) || (is_bag_constraint conseq) then
		(called_prover :="mona " ; Mona.imply ante conseq imp_no)
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
        Mona.imply ante conseq imp_no
      else
        Redlog.imply ante conseq imp_no
  | ZM -> 
      if (is_bag_constraint ante) || (is_bag_constraint conseq) then
        Mona.imply ante conseq imp_no
      else
        Smtsolver.imply ante conseq
  in let _ = if !print_implication then print_string ("CHECK IMPLICATION:\n" ^ (Cprinter.string_of_pure_formula ante) ^ " |- " ^ (Cprinter.string_of_pure_formula conseq) ^ "\n" ^ "res: " ^ (string_of_bool r) ^ "\n") in
  r

let tp_imply_no_cache ante conseq imp_no timeout process =
  let pr = Cprinter.string_of_pure_formula in
  Gen.Debug.ho_2 "tp_imply_no_cache" pr pr string_of_bool
	(fun ante conseq -> tp_imply_no_cache ante conseq imp_no timeout process) ante conseq
;;
(*
let tp_imply_no_cache ante conseq imp_no timeout process =
  if !do_slicing then (* Slicing *)
	let flatten_f = CP.partition_dnf_lhs (CP.trans_dnf ante) in

	let rec prove_lhs_conj ante_conj conseq = match ante_conj with
		| [] -> true
		| h::rest ->
			let rel_constrs = CP.find_relevant_constraints h (CP.fv conseq) in
			let bl = List.flatten (List.map (fun (_,_,bl) -> bl) rel_constrs) in
			let r =
			  if ((List.length bl) = 0) then true (* TODO *)
			  else
				let s_ante = List.fold_left (fun a b -> CP.mkAnd a (CP.BForm (b, None)) no_pos) (CP.mkTrue no_pos) bl in

				let str_lhs = "LHS: " ^ (Cprinter.string_of_pure_formula s_ante) ^ "\n" in
				let str_rhs = "RHS: " ^ (Cprinter.string_of_pure_formula conseq) ^ "\n" in
				let _ = print_string ("tp_imply_no_cache with slicing:\n" ^ str_lhs ^ str_rhs) in
				
				tp_imply_no_cache s_ante conseq imp_no timeout process
			in
			if r then
			  prove_lhs_conj rest conseq
			else r
	  in prove_lhs_conj flatten_f conseq
  else
	tp_imply_no_cache ante conseq imp_no timeout process  
*)
let imply_cache  = Hashtbl.create 2000 ;;
let impl_conseq_cache  = Hashtbl.create 2000 ;;

let add_conseq_to_cache s = 
  try
    let _ = Hashtbl.find impl_conseq_cache s in ()
  with
    | Not_found -> 
          (Gen.Profiling.inc_counter "impl_conseq_count";
          Hashtbl.add impl_conseq_cache s ()
          )
          
let tp_imply ante conseq imp_no timeout process =
  if !Globals.no_cache_formula then
    tp_imply_no_cache ante conseq imp_no timeout process
  else
    (*let _ = Gen.Profiling.push_time "cache overhead" in*)
    let f = CP.mkOr conseq (CP.mkNot ante None no_pos) None no_pos in
    let sf = simplify_var_name f in
    let fstring = Cprinter.string_of_pure_formula sf in
    (*let _ = Gen.Profiling.pop_time "cache overhead" in*)
    let res = 
      try
        Hashtbl.find !impl_cache fstring
      with Not_found ->
        let r = tp_imply_no_cache ante conseq imp_no timeout process in
        (*let _ = Gen.Profiling.push_time "cache overhead" in*)
        let _ = Hashtbl.add !impl_cache fstring r in
        (*let _ = Gen.Profiling.pop_time "cache overhead" in*)
        r
    in res
    
let tp_imply ante conseq imp_no timeout do_cache process =
  (* let _ = print_string ("\nTPdispatcher.ml: tp_imply") in *)
  if !Globals.enable_prune_cache (*&& do_cache*) then
    (
    Gen.Profiling.inc_counter "impl_cache_count";
    add_conseq_to_cache (!print_pure conseq) ;
    let s_rhs = !print_pure conseq in
    let s = (!print_pure ante)^"/"^ s_rhs in
    try 
      let r = Hashtbl.find imply_cache s in
      (* print_string ("hit rhs: "^s_rhs^"\n");*)
      r
      with Not_found -> 
        let r = tp_imply_no_cache ante conseq imp_no timeout process in
        (Hashtbl.add imply_cache s r ;
         (*print_string ("s rhs: "^s_rhs^"\n");*)
         Gen.Profiling.inc_counter "impl_proof_count";
        r))
  else  
    tp_imply ante conseq imp_no timeout process
;;

let tp_imply ante conseq imp_no timeout do_cache process =
  let pr = Cprinter.string_of_pure_formula in
  Gen.Debug.ho_2 "tp_imply" pr pr string_of_bool
	(fun ante conseq -> tp_imply ante conseq imp_no timeout do_cache process) ante conseq

let tp_imply_debug ante conseq imp_no timeout do_cache process =
  Gen.Debug.no_6 "tp_imply " 
      Cprinter.string_of_pure_formula 
      Cprinter.string_of_pure_formula
      (fun c-> c) (fun _ -> "?") string_of_bool (fun _ -> "?")
      string_of_bool 
      tp_imply ante conseq imp_no timeout do_cache process

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
  | CP.BForm ((CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _), _), _) ->
      List.map (fun x -> if x <> formula then CP.subst [v1, v2] x else x) list
  | CP.BForm ((CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _), _), _) ->
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
        | CP.BForm ((CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _), _), _) -> CP.subst [v1, v2]
        | CP.BForm ((CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _), _), _) -> CP.subst_term [v1, term]
        | CP.BForm ((CP.Eq ((CP.IConst(i, _) as term), CP.Var (v1, _), _), _), _) -> CP.subst_term [v1, term]
        | _ -> fun x -> x
      in
      if ((not rid) && x = rform) then (x, subst_fun) else (subst_fun x, subst_fun)
;;

let is_irrelevant = function
  | CP.BForm ((CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _), _), _) -> v1 = v2
  | CP.BForm ((CP.Eq (CP.IConst(i1, _), CP.IConst(i2, _), _), _), _) -> i1 = i2
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
  let l1 = CP.remove_dups_svl (l1 @ (CP.bag_vars_formula conseq)) in
  let antes = split_conjunctions ante in
  let fold_fun l_f_vars (ante, conseq)  = function
    | CP.BForm ((CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _), _), _) ->
        ((CP.subst [v1, v2] ante, CP.subst [v1, v2] conseq), (CP.subst [v1, v2]))
    | CP.BForm ((CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _), _), _)
    | CP.BForm ((CP.Eq ((CP.IConst(i, _) as term), CP.Var (v1, _), _), _), _) ->
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

let is_sat (f: CP.formula) (sat_no: string) do_cache: bool =
  proof_no := !proof_no+1 ;
  let sat_no = (string_of_int !proof_no) in
  Debug.devel_pprint ("SAT #" ^ sat_no) no_pos;
  Debug.devel_pprint (!print_pure f) no_pos;
  let f = elim_exists f in
  if (CP.isConstTrue f) then true 
  else if (CP.isConstFalse f) then false
  else
	let (f, _) = simpl_pair true (f, CP.mkFalse no_pos) in
	tp_is_sat f sat_no do_cache
;;

let is_sat (f : CP.formula) (sat_no : string) do_cache: bool =
  Gen.Debug.ho_1 "is_sat"  Cprinter.string_of_pure_formula string_of_bool (fun _ -> is_sat f sat_no do_cache) f
(*
let imply_timeout_orig (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout do_cache process
	: bool*(formula_label option * formula_label option )list * (formula_label option) = (*result+successfull matches+ possible fail*)
  (* let _ = print_string ("\nTpdispatcher.ml: imply_timeout begining") in *)
  proof_no := !proof_no + 1 ; 
  let imp_no = (string_of_int !proof_no) in
  (* let _ = print_string ("\nTPdispatcher.ml: imply_timeout:" ^ imp_no) in *)
  Debug.devel_pprint ("IMP #" ^ imp_no) no_pos;  
  Debug.devel_pprint ("ante: " ^ (!print_pure ante0)) no_pos;
  Debug.devel_pprint ("conseq: " ^ (!print_pure conseq0)) no_pos;
  if !external_prover then 
    match Netprover.call_prover (Imply (ante0,conseq0)) with
        Some res -> (res,[],None)       
      | None -> (false,[],None)
  else begin 
	(*let _ = print_string ("Imply: => " ^(Cprinter.string_of_pure_formula ante0)^"\n==> "^(Cprinter.string_of_pure_formula conseq0)^"\n") in*)
	let conseq = if CP.should_simplify conseq0 then simplify_a 12 conseq0 else conseq0 in
	if CP.isConstTrue conseq then (true, [],None)
	else
      let ante = if CP.should_simplify ante0 then simplify_a 13 ante0 else ante0 in
	  if (* CP.isConstFalse ante0 || *) CP.isConstFalse ante then (true,[],None)
	  else
        (* let _ = print_string ("\nTpdispatcher.ml: imply_timeout bef elim exist ante") in *)
		let ante = elim_exists ante in
        (* let _ = print_string ("\nTpdispatcher.ml: imply_timeout after elim exist ante") in *)
		(*let conseq = elim_exists conseq in*) (*TODO*)
		let split_conseq = split_conjunctions conseq in
		let pairs = List.map (fun cons -> 
          let (ante,cons) = simpl_pair false (requant ante, requant cons) in 
          let ante = CP.remove_dup_constraints ante in
          match process with
            | Some (Some proc, true) -> (ante, cons) (* don't filter when in incremental mode - need to send full ante to prover *)
            | _ -> filter ante cons
		) split_conseq in
		let pairs_length = List.length pairs in
		let imp_sub_no = ref 0 in
        (* let _ = (let _ = print_string("\n!!!!!!! bef\n") in flush stdout ;) in *)
		let fold_fun (res1,res2,res3) (ante, conseq) =
		  (incr imp_sub_no;
		   if res1 then 
            (*<< for log - numbering *)
			 let imp_no = 
			   if pairs_length > 1 then ( (* let _ = print_string("\n!!!!!!! \n") in flush stdout ; *) (imp_no ^ "." ^ string_of_int (!imp_sub_no)))
			   else imp_no in
            (*>> for log - numbering *)
            (*<< test the pair for implication - implication result is saved in res1*)
			 let res1 =
			   if (not (CP.is_formula_arith ante)) && (CP.is_formula_arith conseq) then 
				 let res1 = tp_imply(*_debug*) (CP.drop_bag_formula ante) conseq imp_no timeout do_cache process in
				 if res1 then res1
				 else tp_imply(*_debug*) ante conseq imp_no timeout do_cache process
			   else tp_imply(*_debug*) ante conseq imp_no timeout do_cache process in
			 let l1 = CP.get_pure_label ante in
             let l2 = CP.get_pure_label conseq in
            (* let _ = print_string ("\n!!! " ^ (* (Cprinter.string_of_formula_label l1 "") *) str^ " \n") in *)
			 if res1 then (res1,(l1,l2)::res2,None)
			 else (res1,res2,l2)
          (*>> test the pair for implication - implication result is saved in res1*)
		   else (res1,res2,res3))
		in
        (* let _ = print_string ("\nTpdispatcher.ml: imply_timeout end") in *)
		List.fold_left fold_fun (true,[],None) pairs
  end;
;;
*)
let imply_timeout (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout do_cache process
	: bool*(formula_label option * formula_label option )list * (formula_label option) = (*result+successfull matches+ possible fail*)
	(* let _ = print_string ("\nTpdispatcher.ml: imply_timeout begining") in *)
  proof_no := !proof_no + 1 ; 
  let imp_no = (string_of_int !proof_no) in
	(* let _ = print_string ("\nTPdispatcher.ml: imply_timeout:" ^ imp_no) in *)
  Debug.devel_pprint ("IMP #" ^ imp_no) no_pos;  
  Debug.devel_pprint ("ante: " ^ (!print_pure ante0)) no_pos;
  Debug.devel_pprint ("conseq: " ^ (!print_pure conseq0)) no_pos;
  if !external_prover then 
    match Netprover.call_prover (Imply (ante0,conseq0)) with
        Some res -> (res,[],None)       
	  | None -> (false,[],None)
  else begin 
	  (*let _ = print_string ("Imply: => " ^(Cprinter.string_of_pure_formula ante0)^"\n==> "^(Cprinter.string_of_pure_formula conseq0)^"\n") in*)
	let conseq = if CP.should_simplify conseq0 then simplify_a 12 conseq0 else conseq0 in
	if CP.isConstTrue conseq then (true, [],None)
	else
	  let ante = if CP.should_simplify ante0 then simplify_a 13 ante0 else ante0 in
	  if (* CP.isConstFalse ante0 || *) CP.isConstFalse ante then (true,[],None)
	  else
          (* let _ = print_string ("\nTpdispatcher.ml: imply_timeout bef elim exist ante") in *)
		let ante = elim_exists ante in
          (* let _ = print_string ("\nTpdispatcher.ml: imply_timeout after elim exist ante") in *)
		  (*let conseq = elim_exists conseq in*) (*TODO*)
		let split_conseq = split_conjunctions conseq in
		let pairs = List.map (fun cons -> 
		  let (ante,cons) = simpl_pair false (requant ante, requant cons) in 
		  let ante = CP.remove_dup_constraints ante in
		  match process with
            | Some (Some proc, true) -> ([ante], cons) (* don't filter when in incremental mode - need to send full ante to prover *)
            | _ -> filter ante cons
		) split_conseq in
		let pairs_length = List.length pairs in
		let imp_sub_no = ref 0 in
          (* let _ = (let _ = print_string("\n!!!!!!! bef\n") in flush stdout ;) in *)
		let fold_fun (res1,res2,res3) (ante, conseq) =
		  (incr imp_sub_no;
		   if res1 then 
               (*<< for log - numbering *)
			 let imp_no = 
			   if pairs_length > 1 then ( (* let _ = print_string("\n!!!!!!! \n") in flush stdout ; *) (imp_no ^ "." ^ string_of_int (!imp_sub_no)))
			   else imp_no in
               (*>> for log - numbering *)
               (*<< test the pair for implication - implication result is saved in res1*)
			 let res1 = List.fold_left (fun acc s_ante -> if not acc then acc else
				 if (not (CP.is_formula_arith s_ante)) && (CP.is_formula_arith conseq) then 
				   let res1 = tp_imply(*_debug*) (CP.drop_bag_formula s_ante) conseq imp_no timeout do_cache process in
				   if res1 then res1
				   else tp_imply(*_debug*) s_ante conseq imp_no timeout do_cache process
				 else tp_imply(*_debug*) s_ante conseq imp_no timeout do_cache process) true ante
			 in 						  
			 let l1 = CP.get_pure_label (List.hd ante) in
             let l2 = CP.get_pure_label conseq in
               (* let _ = print_string ("\n!!! " ^ (* (Cprinter.string_of_formula_label l1 "") *) str^ " \n") in *)
			 if res1 then (res1,(l1,l2)::res2,None)
			 else (res1,res2,l2)
			 (*>> test the pair for implication - implication result is saved in res1*)
		   else (res1,res2,res3))
		in
          (* let _ = print_string ("\nTpdispatcher.ml: imply_timeout end") in *)
		List.fold_left fold_fun (true,[],None) pairs
  end;
;;

let imply_timeout (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout do_cache process
	  : bool*(formula_label option * formula_label option )list * (formula_label option) (*result+successfull matches+ possible fail*)
  = let pf = Cprinter.string_of_pure_formula in
  Gen.Debug.ho_2 "imply_timeout" pf pf (fun (b,_,_) -> string_of_bool b)
      (fun a c -> imply_timeout a c imp_no timeout do_cache process) ante0 conseq0
(*
let imply_timeout_original (ante0 : CP.formula) (conseq0 : CP.formula) (imp_no : string) timeout do_cache
	: bool*(formula_label option * formula_label option )list * (formula_label option) = (*result+successfull matches+ possible fail*)
  proof_no := !proof_no + 1 ; 
  let imp_no = (string_of_int !proof_no) in
  Debug.devel_pprint ("IMP #" ^ imp_no) no_pos;  
  Debug.devel_pprint ("ante: " ^ (!print_pure ante0)) no_pos;
  Debug.devel_pprint ("conseq: " ^ (!print_pure conseq0)) no_pos;
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
;;*)

let imply_timeout ante0 conseq0 imp_no timeout do_cache process =
  let s = "imply" in
  let _ = Gen.Profiling.push_time s in
  let (res1,res2,res3) = imply_timeout ante0 conseq0 imp_no timeout do_cache process in
  let _ = Gen.Profiling.pop_time s in
  if res1  then Gen.Profiling.inc_counter "true_imply_count" else Gen.Profiling.inc_counter "false_imply_count" ; 
  (res1,res2,res3)
	
let disj_cnt a c s =
  if (!Globals.enable_counters) then
	begin
	  let rec p_f_size f = match f with
		| CP.BForm _ -> 1
		| CP.And (f1,f2,_) | CP.Or (f1,f2,_,_) -> (p_f_size f1)+(p_f_size f2)
		| CP.Not (f,_,_) | CP.Forall (_,f,_,_ ) | CP.Exists (_,f,_,_) -> p_f_size f in

	  let rec or_f_size f = match f with
		| CP.BForm _ -> 1
		| CP.And (f1,f2,_) -> (or_f_size f1)*(or_f_size f2)
		| CP.Or (f1,f2,_,_) -> (or_f_size f1)+(or_f_size f2)
		| CP.Not (f,_,_) | CP.Forall (_,f,_,_ ) | CP.Exists (_,f,_,_) -> or_f_size f in
     (*Gen.Profiling.add_to_counter "imply_disj_count_ante" (or_f_size ante0);
       Gen.Profiling.add_to_counter "imply_disj_count_conseq" (or_f_size conseq0);
       Gen.Profiling.inc_counter "imply_count";
       Gen.Profiling.add_to_counter "imply_size_count" ((p_f_size ante0)+(p_f_size conseq0))*) 
      let rec add_or_f_size f = match f with
		| CP.BForm _ -> 0
		| CP.And (f1,f2,_) -> (add_or_f_size f1)+(add_or_f_size f2)
		| CP.Or (f1,f2,_,_) -> 1+(add_or_f_size f1)+(add_or_f_size f2)
		| CP.Not (f,_,_) | CP.Forall (_,f,_,_ ) | CP.Exists (_,f,_,_) -> add_or_f_size f in
      match c with
		| None -> 
          Gen.Profiling.inc_counter ("stat_count_"^s);
          Gen.Profiling.add_to_counter ("z_stat_disj_"^s) (1+(add_or_f_size a));
          Gen.Profiling.add_to_counter ("stat_disj_count_"^s) (or_f_size a);
          Gen.Profiling.add_to_counter ("stat_size_count_"^s) (p_f_size a)
		| Some c-> 
          Gen.Profiling.inc_counter ("stat_count_"^s);
          Gen.Profiling.add_to_counter ("z_stat_disj_"^s) (1+(add_or_f_size a)); 
          Gen.Profiling.add_to_counter ("stat_disj_count_"^s) ((or_f_size a)+(or_f_size c));
          Gen.Profiling.add_to_counter ("stat_size_count_"^s) ((p_f_size a)+(p_f_size c)) ;
    end
  else ()

let imply_timeout a c i t dc process =
  disj_cnt a (Some c) "imply";
  Gen.Profiling.do_5 "TP.imply_timeout" imply_timeout a c i t dc process
	
let memo_imply_timeout ante0 conseq0 imp_no timeout = 
  (* let _ = print_string ("\nTPdispatcher.ml: memo_imply_timeout") in *)
  let _ = Gen.Profiling.push_time "memo_imply" in
  let r = List.fold_left (fun (r1,r2,r3) c->
    if not r1 then (r1,r2,r3)
    else 
      let l = List.filter (fun d -> (List.length (Gen.BList.intersect_eq CP.eq_spec_var c.MCP.memo_group_fv d.MCP.memo_group_fv))>0) ante0 in
      let ant = MCP.fold_mem_lst_m (CP.mkTrue no_pos) true (*!no_LHS_prop_drop*) true l in
      let con = MCP.fold_mem_lst_m (CP.mkTrue no_pos) !no_RHS_prop_drop false [c] in
      let r1',r2',r3' = imply_timeout ant con imp_no timeout false None in 
      (r1',r2@r2',r3')) (true, [], None) conseq0 in
  let _ = Gen.Profiling.pop_time "memo_imply" in
  r

let memo_imply_timeout ante0 conseq0 imp_no timeout =
  Gen.Debug.ho_2 "memo_imply_timeout"
	(Cprinter.string_of_memoised_list)
	(Cprinter.string_of_memoised_list)
	(fun (r,_,_) -> string_of_bool r)
	(fun a c -> memo_imply_timeout a c imp_no timeout) ante0 conseq0
	
let mix_imply_timeout ante0 conseq0 imp_no timeout = 
  (* let _ = print_string ("\nTPdispatcher.ml: mix_imply_timeout") in *)
  match ante0,conseq0 with
	| MCP.MemoF a, MCP.MemoF c -> memo_imply_timeout a c imp_no timeout
    | MCP.OnePF a, MCP.OnePF c -> imply_timeout a c imp_no timeout false None
	| _ -> report_error no_pos ("mix_imply_timeout: mismatched mix formulas ")

let rec imply ante0 conseq0 imp_no do_cache process =
  Gen.Debug.ho_2 "imply" (Cprinter.string_of_pure_formula) (Cprinter.string_of_pure_formula) 
    (fun (r, _, _) -> string_of_bool r)
    (fun ante0 conseq0 -> imply_x ante0 conseq0 imp_no do_cache process) ante0 conseq0

and imply_x ante0 conseq0 imp_no do_cache process = imply_timeout ante0 conseq0 imp_no 0. do_cache process
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
    disj_cnt f None "sat";
    Gen.Profiling.do_1 "is_sat" (is_sat f sat_no) do_cache
  end
;;

let sat_no = ref 1
;;

let incr_sat_no () = 
 sat_no := !sat_no +1 
;;

let is_sat_sub_no_c (f : CP.formula) sat_subno do_cache : bool = 
  let sat = is_sat f ((string_of_int !sat_no) ^ "." ^ (string_of_int !sat_subno)) do_cache in
  (* Debug.devel_pprint ("SAT #" ^ (string_of_int !sat_no) ^ "." ^ (string_of_int !sat_subno)) no_pos; *)
  sat_subno := !sat_subno+1;
  sat
;;

let is_sat_sub_no_with_slicing (f:CP.formula) sat_subno : bool =
  let overlap (nlv1, lv1) (nlv2, lv2) =
	(*
	if (nlv1 = [] && nlv2 = []) then
	  (Gen.BList.list_equiv_eq CP.eq_spec_var lv1 lv2)
	else
	  (Gen.BList.overlap_eq CP.eq_spec_var nlv1 nlv2) && (Gen.BList.list_equiv_eq CP.eq_spec_var lv1 lv2)
	*)
	if (nlv1 = [] && nlv2 = []) then
	  (Gen.BList.list_equiv_eq CP.eq_spec_var lv1 lv2)
	else
	  (Gen.BList.overlap_eq CP.eq_spec_var nlv1 nlv2)
  in
  
  let rec group_conj l = match l with
    | [] -> (false,[]) 
    | ((f_nlv, f_lv), fs)::t ->  
      let b,l = group_conj t in
      let l1, l2 = List.partition (fun (cfv, _) -> overlap (f_nlv, f_lv) cfv) l in
      if l1==[] then (b,((f_nlv, f_lv), fs)::l) 
      else 
        let l_fv, nfs = List.split l1 in
		let l_nlv, l_lv = List.split l_fv in
        let nfs = CP.join_conjunctions (fs::nfs) in
        let n_nlv = CP.remove_dups_svl (List.concat (f_nlv::l_nlv)) in
		let n_lv = CP.remove_dups_svl (List.concat (f_lv::l_lv)) in
        (true,((n_nlv, n_lv), nfs)::l2)
  in
  
  let rec fix n_l = 
    let r1, r2 = group_conj n_l in
    if r1 then fix r2 else r2
  in    

  let split_sub_f f = 
    let conj_list = CP.split_conjunctions f in
    let n_l = List.map
	  (fun c -> (CP.fv_with_slicing_label c, c)) conj_list in
    snd (List.split (fix n_l))
  in

  let n_f = CP.elim_exists_with_fresh_vars f in

  let _ = print_string ("is_sat_sub_no_with_slicing: f: " ^ (Cprinter.string_of_pure_formula f) ^ "\n") in
  let _ = print_string ("is_sat_sub_no_with_slicing: n_f: " ^ (Cprinter.string_of_pure_formula n_f) ^ "\n") in

  let dnf_f = CP.dnf_to_list f in

  let _ = print_string ("is_sat_sub_no_with_slicing: dnf_f: " ^
    (List.fold_left (fun acc f -> acc ^ "+++++++++\n" ^ (Cprinter.string_of_pure_formula f) ^ "\n") "" dnf_f)) in
  (*
  let n_f_l = split_sub_f n_f in

  let _ = print_string ("is_sat_sub_no_with_slicing: n_f_l: " ^
    (List.fold_left (fun acc f -> acc ^ "+++++++++\n" ^ (Cprinter.string_of_pure_formula f) ^ "\n") "" n_f_l)) in
  
  List.fold_left (fun a f -> if not a then a else is_sat_sub_no_c f sat_subno false) true n_f_l
  *)

  let is_related f1 f2 =
	let (nlv1, lv1) = CP.fv_with_slicing_label f1 in
	let fv = CP.fv f2 in
	if (nlv1 == []) then
	  Gen.BList.overlap_eq CP.eq_spec_var fv lv1
	else
	  Gen.BList.overlap_eq CP.eq_spec_var fv nlv1
  in 

  let pick_rel_constraints f f_l =
	List.find_all (fun fs -> fs != f && is_related fs f) f_l
  in 
  
  let check_sat f =
	let n_f_l = split_sub_f f in

	let _ = print_string ("is_sat_sub_no_with_slicing: n_f_l: " ^
    (List.fold_left (fun acc f -> acc ^ "+++++++++\n" ^ (Cprinter.string_of_pure_formula f) ^ "\n") "" n_f_l)) in

	List.fold_left (fun a f ->
	  if not a then a
	  else is_sat_sub_no_c (CP.join_conjunctions (f::(pick_rel_constraints f n_f_l))) sat_subno false) true n_f_l
  in
  List.fold_left (fun a f -> if a then a else check_sat f) false dnf_f
	

let is_sat_sub_no_with_slicing (f:CP.formula) sat_subno : bool =
  Gen.Debug.ho_1 "is_sat_sub_no_with_slicing"
	Cprinter.string_of_pure_formula
	string_of_bool
	(fun f -> is_sat_sub_no_with_slicing f sat_subno) f

let is_sat_sub_no (f : CP.formula) sat_subno : bool =
  (*is_sat_sub_no_c f sat_subno false*)
  is_sat_sub_no_with_slicing f sat_subno

let is_sat_sub_no (f : CP.formula) sat_subno : bool =  
  Gen.Debug.ho_2 "is_sat_sub_no" (Cprinter.string_of_pure_formula) (fun x-> string_of_int !x)
    (string_of_bool ) is_sat_sub_no f sat_subno;;
	
let is_sat_memo_sub_no (f : MCP.memo_pure) sat_subno with_dupl with_inv : bool = 
  let f_lst = MCP.fold_mem_lst_to_lst f with_dupl with_inv true in
  if !f_2_slice then (is_sat_sub_no (CP.join_conjunctions f_lst) sat_subno)
  else not (List.fold_left (fun a c-> if a then a else not (is_sat_sub_no c sat_subno)) false f_lst)

let is_sat_memo_sub_no (f : MCP.memo_pure) sat_subno with_dupl with_inv : bool =
  Gen.Debug.ho_1 "is_sat_memo_sub_no"
	Cprinter.string_of_memo_pure_formula
	string_of_bool
	(fun f -> is_sat_memo_sub_no f sat_subno with_dupl with_inv) f

let is_sat_mix_sub_no (f : MCP.mix_formula) sat_subno with_dupl with_inv : bool = match f with
  | MCP.MemoF f -> is_sat_memo_sub_no f sat_subno with_dupl with_inv
  | MCP.OnePF f -> (if !do_sat_slice then is_sat_sub_no_with_slicing else is_sat_sub_no) f sat_subno

let is_sat_mix_sub_no (f : MCP.mix_formula) sat_subno with_dupl with_inv =
  Gen.Debug.ho_1 "is_sat_mix_sub_no"
	Cprinter.string_of_mix_formula
	string_of_bool
	(fun f -> is_sat_mix_sub_no f sat_subno with_dupl with_inv) f

let is_sat_msg_no_no prof_lbl (f:CP.formula) do_cache :bool = 
  let sat_subno = ref 0 in
  let _ = Gen.Profiling.push_time prof_lbl in
  let sat = is_sat_sub_no_c f sat_subno do_cache in
  let _ = Gen.Profiling.pop_time prof_lbl in
  sat
  
let imply_sub_no ante0 conseq0 imp_no do_cache =
  Debug.devel_pprint ("IMP #" ^ imp_no ^ "\n") no_pos;
  (* imp_no := !imp_no+1;*)
  imply ante0 conseq0 imp_no do_cache

let imply_msg_no_no ante0 conseq0 imp_no prof_lbl do_cache =
  let _ = Gen.Profiling.push_time prof_lbl in  
  let r = imply_sub_no ante0 conseq0 imp_no do_cache in
  let _ = Gen.Profiling.pop_time prof_lbl in
  r

(* is below called by pruning *)
let imply_msg_no_no ante0 conseq0 imp_no prof_lbl do_cache process =
Gen.Debug.no_2 "imply_msg_no_no " 
  Cprinter.string_of_pure_formula 
  Cprinter.string_of_pure_formula
 (fun (x,_,_)-> string_of_bool x) 
 (fun _ _ -> imply_msg_no_no ante0 conseq0 imp_no prof_lbl do_cache process) ante0 conseq0
  
let print_stats () =
  print_string ("\nTP statistics:\n");
  print_string ("omega_count = " ^ (string_of_int !omega_count) ^ "\n")

let start_prover () =
  (* let _ = print_string ("\n Tpdispatcher: start_prover \n") in *)
  match !tp with
  | Coq -> begin
      Coq.start ();
	  Omega.start ();
	 end
  | Redlog | RM -> 
    begin
      Redlog.start ();
	  Omega.start ();
	 end
  | Cvc3 -> 
        begin
            provers_process := Some (Cvc3.start ()); (* because of incremental *)
            let _ = match !provers_process with 
              |Some proc ->  !incremMethodsO#set_process proc
              | _ -> () in
	        Omega.start ();
	    end
  | Mona ->
        Mona.start()
  | Isabelle ->
     begin
      Isabelle.start();
	  Omega.start();
     end
  | _ -> Omega.start()
  
let stop_prover () =
  match !tp with
    | Coq -> (* Coq.stop_prover () *)
          begin
            Coq.stop ();
	        Omega.stop();
	      end
    | Redlog | RM -> 
          begin
            Redlog.stop();
	        Omega.stop();
	      end
    | Cvc3 -> 
          begin
            match !provers_process with
              |Some proc ->  Cvc3.stop proc;
              |_ -> ();
	        Omega.stop();
	      end
    | Isabelle -> 
          begin
            Isabelle.stop();
	        Omega.stop();
	      end
    | Mona -> Mona.stop();
    | _ -> Omega.stop();;

let prover_log = Buffer.create 5096

let get_prover_log () = Buffer.contents prover_log
let clear_prover_log () = Buffer.clear prover_log

let change_prover prover =
  clear_prover_log ();
  tp := prover;
  start_prover ()
