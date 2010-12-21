(*
  Call Omega Calculator, send input to it
*)
open Globals
open Cpure
exception Timeout

let channels = ref (stdin, stdout)
let omega_call_count: int ref = ref 0
let is_omega_running = ref false
let timeout = ref 15.0 (* default timeout is 15 seconds *)
let omega_pid = ref 0

(***********)
let test_number = ref 0
let last_test_number = ref 0
let log_all_flag = ref false
let log_all = open_out ("allinput.oc" (* ^ (string_of_int (Unix.getpid ())) *) )

(* currently not used --should be removed*)
let infilename = ref (!tmp_files_path ^ "input.oc." ^ (string_of_int (Unix.getpid ())))
let resultfilename = ref (!tmp_files_path ^ "result.txt." ^ (string_of_int (Unix.getpid())))

let init_files () =
  begin
	infilename := "input.oc." ^ (string_of_int (Unix.getpid ()));
	resultfilename := "result.txt." ^ (string_of_int (Unix.getpid()));
  end

let omega_of_spec_var (sv : spec_var):string = match sv with
  | SpecVar (t, v, p) -> 
		let r = match (List.filter (fun (a,b,_)-> ((String.compare v b)==0) )!Ocparser.subst_lst) with
				  | []->           
            let ln = (String.length v) in  
            let r_c = if (ln<15) then v
              else 
                let v_s = String.sub v (ln-15)  15 in
                if((String.get v_s 0)=='_') then String.sub v_s 1 ((String.length v_s)-1) else v_s in
            begin
              Ocparser.subst_lst := (r_c,v,t)::!Ocparser.subst_lst; 
							r_c end
					| (a,b,_)::h->  a in 
		r ^ (if is_primed sv then Oclexer.primed_str else "")
		
	

let rec omega_of_exp e0 = match e0 with
  | Null _ -> "0"
  | Var (sv, _) -> omega_of_spec_var sv
  | IConst (i, _) -> string_of_int i 
  | Add (a1, a2, _) ->  (omega_of_exp a1)^ " + " ^(omega_of_exp a2) 
  | Subtract (a1, a2, _) ->  (omega_of_exp a1)^ " - " ^(omega_of_exp a2)
  | Mult (a1, a2, l) ->
      let r = match a1 with
        | IConst (i, _) -> (string_of_int i) ^ "(" ^ (omega_of_exp a2) ^ ")"
        | _ -> let rr = match a2 with
            | IConst (i, _) -> (string_of_int i) ^ "(" ^ (omega_of_exp a1) ^ ")"
            | _ -> 
                Error.report_warning {
                  Error.error_loc = l;
                  Error.error_text = "[omega.ml] Non-linear arithmetic is not supported by Omega."
                }
            in rr
      in r
  | Div (_, _, l) -> 
      Error.report_warning {
        Error.error_loc = l;
        Error.error_text ="[omega.ml] Divide is not supported."
      }
  | Max _
  | Min _ -> failwith ("Omega.omega_of_exp: min/max should not appear here")
  | _ -> failwith ("Omega.omega_of_exp: bag or list constraint")

and omega_of_b_formula b = match b with
  | BConst (c, _) -> if c then "(0=0)" else "(0>0)"
  | BVar (bv, _) ->  (omega_of_spec_var bv) ^ " > 0"
  | Lt (a1, a2, _) ->(omega_of_exp a1) ^ " < " ^ (omega_of_exp a2)
  | Lte (a1, a2, _) -> (omega_of_exp a1) ^ " <= " ^ (omega_of_exp a2)
  | Gt (a1, a2, _) ->  (omega_of_exp a1) ^ " > " ^ (omega_of_exp a2)
  | Gte (a1, a2, _) -> (omega_of_exp a1) ^ " >= " ^ (omega_of_exp a2)
  | Eq (a1, a2, _) -> begin
        if is_null a2 then	(omega_of_exp a1)^ " < 1"
        else if is_null a1 then (omega_of_exp a2) ^ " < 1"
        else  				(omega_of_exp a1) ^ " = " ^ (omega_of_exp a2)
  end
  | Neq (a1, a2, _) -> begin
        if is_null a2 then
        				(omega_of_exp a1) ^ " > 0"
        else if is_null a1 then						
        				(omega_of_exp a2) ^ " > 0"
        else		(omega_of_exp a1)^ " != " ^ (omega_of_exp a2)
    end
  | EqMax (a1, a2, a3, _) ->
      let a1str = omega_of_exp a1 in
      let a2str = omega_of_exp a2 in
      let a3str = omega_of_exp a3 in
        "((" ^ a2str ^ " >= " ^ a3str ^ " & " ^ a1str ^ " = " ^ a2str ^ ") | ("
        ^ a3str ^ " > " ^ a2str ^ " & " ^ a1str ^ " = " ^ a3str ^ "))"
  | EqMin (a1, a2, a3, _) ->
      let a1str = omega_of_exp a1  in
      let a2str = omega_of_exp a2  in
      let a3str = omega_of_exp a3  in
        "((" ^ a2str ^ " >= " ^ a3str ^ " & " ^ a1str ^ " = " ^ a3str ^ ") | ("
        ^ a3str ^ " > " ^ a2str ^ " & " ^ a1str ^ " = " ^ a2str ^ "))"
  | _ -> failwith ("Omega.omega_of_exp: bag or list constraint")
 
and omega_of_formula f  = match f with
  | BForm (b,_) -> 		"(" ^ (omega_of_b_formula b) ^ ")"
  | And (p1, p2, _) -> 	"(" ^ (omega_of_formula p1) ^ " & " ^ (omega_of_formula p2 ) ^ ")"
  | Or (p1, p2,_ , _) -> 	"(" ^ (omega_of_formula p1) ^ " | " ^ (omega_of_formula p2) ^ ")"
  | Not (p,_ , _) ->       " (not (" ^ (omega_of_formula p) ^ ")) "	
  | Forall (sv, p,_ , _) -> " (forall (" ^ (omega_of_spec_var sv) ^ ":" ^ (omega_of_formula p) ^ ")) "
  | Exists (sv, p,_ , _) -> " (exists (" ^ (omega_of_spec_var sv) ^ ":" ^ (omega_of_formula p) ^ ")) "


let omegacalc = "oc" (* TODO: fix oc path *)
(*let omegacalc = "/home/locle/workspace/omega/omega_calc/obj/oc"*)

let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout)
let start_with str prefix =
  (String.length str >= String.length prefix) && (String.sub str 0 (String.length prefix) = prefix) 
let send_cmd cmd =
  if !is_omega_running then output_string (snd !channels) (cmd ^ "\n")

let set_timer tsecs =
  ignore (Unix.setitimer Unix.ITIMER_REAL
            { Unix.it_interval = 0.0; Unix.it_value = tsecs })


(* start omega system in a separated process and load redlog package *)
let start_omega () =
  if not !is_omega_running then begin
    print_string "Starting Omega... \n"; flush stdout;
    last_test_number := !test_number;
	(if !log_all_flag then 
        output_string log_all ("[omega.ml]: >> Starting Omega...\n") );
    let inchanel, outchanel, errchanel, pid = Unix_add.open_process_full omegacalc [|omegacalc|]  (*omegacalc [|omegacalc|]*) in 
	(*let pid = Unix.create_process omegacalc  [|omegacalc|] (Unix.stdin) (snd channels) Unix.stderr in (*open_process*) *) 
	(*let inchanel, outchanel = Unix.open_process (omegacalc) in*)
    channels := inchanel, outchanel; 
	
    is_omega_running := true;
    omega_pid := pid;
    
    let finished = ref false in
    while not !finished do
      let line = input_line (fst !channels) in
	  (*let _ = print_endline line in *)
	  (if !log_all_flag then 
        output_string log_all ("[omega.ml]: >> " ^ line ^ "\nOC is running!\n") );
      if (start_with line "#") then finished := true;
    done;
	
    (*print_endline "OC is running!"; flush stdout*)
  end

(* stop Omega system *)
let stop_omega () = 
  if !is_omega_running then begin
    (*send_cmd "quit;"; flush (snd !channels);*)
    let num_tasks = !test_number - !last_test_number in
    print_string ("Stop Omega... "^(string_of_int num_tasks)^" invocations "); flush stdout;
	(if !log_all_flag then 
        output_string log_all ("[omega.ml]: >> Stop Omega after ... "^(string_of_int num_tasks)^" invocations\n") );
    Unix.kill !omega_pid 9;
    ignore (Unix.waitpid [] !omega_pid);
    is_omega_running := false;
    omega_pid := 0;
  end

(* restart Omega system *)
let restart_omega reason =
  if !is_omega_running then begin
    let num_tasks = !test_number - !last_test_number in
    print_string (reason^" Restarting Omega after ... "^(string_of_int num_tasks)^" invocations ");
	(if !log_all_flag then 
        output_string log_all ("[omega.ml]: >> " ^ reason ^ " Restarting Omega after ... "^(string_of_int num_tasks)^" invocations \n") );
    stop_omega();
    start_omega();
  end

(*
  - in: input channel
  - out: receiving msg
  - Desc: read from the channel, return the msg
*)
let read_from_in_channel chn : string =
  let res = ref "" in
  let quitloop = ref false in
     while not !quitloop do
	  let line = input_line chn in
      let n = String.length line in
        if n > 0 then begin
		 (* print_string (line^"\n"); flush stdout;*)
          (if !log_all_flag then 
            output_string log_all ("[omega.ml]: >> "^line^"\n") );
          if line.[0] != '#' then
		    begin   
              res := !res ^ line;
              if (line.[n-1] == '}') then
		         quitloop := true;			  
            end;
        end;
    done;
	!res

(*
  - in: input channel
  - out: last non-comment line of the input channel
  - Desc: read from the channel, return the last line
*)	
let read_last_line_from_in_channel chn : string =
  let line = ref "" in
  let quitloop = ref false in
     while not !quitloop do
	  line := (input_line chn);
      let n = String.length !line in
        if n > 0 then begin
		 (* print_string (line^"\n"); flush stdout;*)
          (if !log_all_flag then 
            output_string log_all ("[omega.ml]: >> "^(!line)^"\n") );
          if !line.[0] != '#' then
		    begin   
              
              if (!line.[n-1] == '}') then
		         quitloop := true;			  
            end;
        end;
    done;
	!line
  
(* send formula to omega and receive result -true/false*)
let check_formula f timeout=
(*  try*)
 begin
  if not !is_omega_running then
    start_omega ();
  
  (*timer*)
  let old_handler = Sys.signal Sys.sigalrm sigalrm_handler in
  let reset_sigalrm () = Sys.set_signal Sys.sigalrm old_handler in
  set_timer timeout;
  
 (*let _ = print_endline "check" in*)
  let _ = incr omega_call_count in
  let new_f = 
  if String.length f > 1024 then
     (Util.break_lines f)
  else
      f
  in
  output_string (snd !channels) new_f;
  flush (snd !channels);
  
  let result = ref true in
  let str = read_last_line_from_in_channel (fst !channels) in
  let n = String.length str in
  if n > 7 then
   begin
    let lastchars = String.sub str (n - 7) 7 in
    if lastchars = "FALSE }" then
	begin
        result := false;
	end;
   end;
  (*turn off timer*)
  set_timer 0.0;
  reset_sigalrm () ;
  !result
 end

(* linear optimization with omega *)
let rec send_and_receive f timeout=
 begin
  (*timer*)
  let old_handler = Sys.signal Sys.sigalrm sigalrm_handler in
  let reset_sigalrm () = Sys.set_signal Sys.sigalrm old_handler in
  set_timer timeout;
  
  if not !is_omega_running then
    start_omega ();
  let new_f = 
  if String.length f > 1024 then
     (Util.break_lines f)
  else
      f
  in
    output_string (snd !channels) new_f;
    flush (snd !channels);
	let str = read_from_in_channel (fst !channels) in
		
    let lex_buf = Lexing.from_string str in
	(*print_string (line^"\n"); flush stdout;*)
    let rel = Ocparser.oc_output (Oclexer.tokenizer "interactive") lex_buf in

    (*turn off timer*)
    set_timer 0.0;
    reset_sigalrm () ;	

    rel 
  
  end
(********************************************************************)
let rec omega_of_var_list (vars : ident list) : string = match vars with
  | [] -> ""
  | [v] -> v
  | v :: rest -> v ^ ", " ^ (omega_of_var_list rest)

let get_vars_formula (p : formula) =
  let svars = fv p in
    List.map omega_of_spec_var svars

(*
  Use Omega Calculator to test if a formula is valid -- some other
  tool may probably be used ...
*)

let is_sat (pe : formula)  (sat_no : string): bool =
  (*print_endline (Util.new_line_str^"#is_sat " ^ sat_no ^ Util.new_line_str);*)
  incr test_number;
  begin
        (*  Cvclite.write_CVCLite pe; *)
        (*  Lash.write pe; *)
	Ocparser.subst_lst := [];
    let fstr = omega_of_formula pe in
    let pvars = get_vars_formula pe in
    let vstr = omega_of_var_list (Util.remove_dups pvars) in
    let fomega =  "{[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Util.new_line_str in
    (*    Debug.devel_print ("fomega:\n" ^ fomega ^ "\n"); *)
	(*test*)
	(*print_endline (Util.break_lines fomega);*)
	
    if !log_all_flag then begin
(*      output_string log_all ("YYY" ^ (Cprinter.string_of_pure_formula pe) ^ "\n");*)
      output_string log_all (Util.new_line_str^"#is_sat " ^ sat_no ^ Util.new_line_str);
      output_string log_all (Util.break_lines fomega);
      flush log_all;
    end;
	
	let sat = 
      try
        check_formula fomega !timeout
      with
      | Timeout ->
	      begin
           restart_omega ("Timeout when checking #is_sat " ^ sat_no ^ "!");
           true
		  end
      | exc -> stop_omega (); raise exc 
    in
  (*   let post_time = Unix.gettimeofday () in *)
  (*   let time = (post_time -. pre_time) *. 1000. in *)
   
    if !log_all_flag = true then begin
      if sat then output_string log_all ("[omega.ml]: unsat "^sat_no ^(string_of_int !test_number)^" --> FAIL\n") else output_string log_all ("[omega.ml]: sat "^sat_no^(string_of_int !test_number)^" --> SUCCESS\n");
    end else ();
    sat
  end

let is_valid (pe : formula) timeout: bool =
  (*print_endline "LOCLE: is_valid";*)
  begin
	Ocparser.subst_lst := [];
    let fstr = omega_of_formula pe in
    let vstr = omega_of_var_list (Util.remove_dups (get_vars_formula pe)) in
    let fomega =  "complement {[" ^ vstr ^ "] : (" ^ fstr ^ ")}" ^ ";" ^ Util.new_line_str in
    (*test*)
	(*print_endline (Util.break_lines fomega);*)
	
    if !log_all_flag then begin
(*                output_string log_all ("YYY" ^ (Cprinter.string_of_pure_formula pe) ^ "\n");*)
                output_string log_all (Util.new_line_str^"#is_valid" ^Util.new_line_str);
                output_string log_all (Util.break_lines fomega);
                flush log_all;
            end;
	
	let sat = 
      try
        not (check_formula (fomega ^ "\n") timeout)
      with
      | Timeout ->
          (*log ERROR ("TIMEOUT");*)
          restart_omega ("Timeout when checking #is_valid ");
          true
      | exc -> stop_omega (); raise exc 
    in
  (*   let post_time = Unix.gettimeofday () in *)
  (*   let time = (post_time -. pre_time) *. 1000. in *)
    
    sat		
  end

let imply (ante : formula) (conseq : formula) (imp_no : string) timeout : bool =
  (*print_endline "LOCLE: imply";*)
  incr test_number;
  (*
    let tmp1 = mkAnd ante (mkNot conseq no_pos) no_pos in
    let fvars = fv tmp1 in
    let tmp2 = mkExists fvars tmp1 no_pos in
    not (is_valid tmp2)
   *)
  let tmp_form = mkOr (mkNot ante None no_pos) conseq None no_pos in
  	
  let result = is_valid tmp_form  timeout in
  if !log_all_flag = true then begin
    if result then 
      output_string log_all ("[omega.ml]: imp #" ^ imp_no ^ "-- test #" ^(string_of_int !test_number)^" --> SUCCESS\n") 
    else 
      output_string log_all ("[omega.ml]: imp "^imp_no^(string_of_int !test_number)^" --> FAIL\n");
  end else ();
  result
  
let rec match_vars (vars_list0 : spec_var list) rel = match rel with
| ConstRel b ->
    if b then
      mkTrue no_pos
    else
      mkFalse no_pos
| BaseRel (aelist0, f0) ->
    let rec match_helper vlist aelist f  = match aelist with
    | [] -> f
    | ae :: rest ->
        let v = List.hd vlist in
        let restvars = List.tl vlist in
        let restf = match_helper restvars rest f in
        let tmp1 = mkEqExp (Var (v, no_pos)) ae no_pos in
        let tmp2 = mkAnd tmp1 restf no_pos in
        tmp2
    in
    if List.length aelist0 != List.length vars_list0 then
      failwith ("match_var: numbers of arguments do not match")
    else
      match_helper vars_list0 aelist0 f0
| UnionRel (r1, r2) ->
    let f1 = match_vars vars_list0 r1 in
    let f2 = match_vars vars_list0 r2 in
    let tmp = mkOr f1 f2 None no_pos in
    tmp

let simplify (pe : formula) : formula =
 (* print_endline "LOCLE: simplify";*)
  begin
    Ocparser.subst_lst := [];
    let fstr = omega_of_formula pe in
    let vars_list = get_vars_formula pe in
    let vstr = omega_of_var_list (Util.remove_dups vars_list) in
    let fomega =  "{[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Util.new_line_str in
	(*test*)
	(*print_endline (Util.break_lines fomega);*)
	
    if !log_all_flag then begin
(*                output_string log_all ("YYY" ^ (Cprinter.string_of_pure_formula pe) ^ "\n");*)
      output_string log_all ("#simplify" ^ Util.new_line_str ^ Util.new_line_str);
      output_string log_all ((Util.break_lines fomega) ^ Util.new_line_str ^ Util.new_line_str);
      flush log_all;
    end;
	
    let simp_f = 
	try
      begin	
	   let rel = send_and_receive fomega 0.0 in
	   match_vars (fv pe) rel
	  end
	with
      | Timeout ->
          (*log ERROR ("TIMEOUT");*)
          restart_omega ("Timeout when checking #simplify ");
          pe
      | exc -> stop_omega (); raise exc 
    in
  (*   let post_time = Unix.gettimeofday () in *)
  (*   let time = (post_time -. pre_time) *. 1000. in *)
  
    simp_f
  end

let pairwisecheck (pe : formula) : formula =
  (*print_endline "LOCLE: pairwisecheck";*)
  begin
		Ocparser.subst_lst := [];
    let fstr = omega_of_formula pe in
        let vars_list = get_vars_formula pe in
    let vstr = omega_of_var_list (Util.remove_dups vars_list) in
    let fomega =  "pairwisecheck {[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Util.new_line_str in
	
	(*test*)
	(*print_endline (Util.break_lines fomega);*)
	
    if !log_all_flag then begin
       output_string log_all ("#pairwisecheck" ^ Util.new_line_str ^ Util.new_line_str);
       output_string log_all ((Util.break_lines fomega) ^ Util.new_line_str ^ Util.new_line_str);
       flush log_all;
    end;
    let rel = send_and_receive fomega 0. in
	  match_vars (fv pe) rel 
  end

let hull (pe : formula) : formula =
  (*print_endline "LOCLE: hull";*)
  begin
		Ocparser.subst_lst := [];
    let fstr = omega_of_formula pe in
        let vars_list = get_vars_formula pe in
    let vstr = omega_of_var_list (Util.remove_dups vars_list) in
     let fomega =  "hull {[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Util.new_line_str in
	
	(*test*)
	(*print_endline (Util.break_lines fomega);*)
	
    if !log_all_flag then begin
       output_string log_all ("#hull" ^ Util.new_line_str ^ Util.new_line_str);
       output_string log_all ((Util.break_lines fomega) ^ Util.new_line_str ^ Util.new_line_str);
       flush log_all;
    end;
    let rel = send_and_receive fomega 0. in
	  match_vars (fv pe) rel
  end

let gist (pe1 : formula) (pe2 : formula) : formula =
  (*print_endline "LOCLE: gist";*)
  begin
		Ocparser.subst_lst := [];
    let fstr1 = omega_of_formula pe1 in
        let fstr2 = omega_of_formula pe2 in
        let vars_list = Util.remove_dups (fv pe1 @ fv pe2) in
				let l1 = List.map omega_of_spec_var vars_list  in
    let vstr = String.concat "," l1  in
    let fomega =  "gist {[" ^ vstr ^ "] : (" ^ fstr1
            ^ ")} given {[" ^ vstr ^ "] : (" ^ fstr2 ^ ")};" ^ Util.new_line_str
        in
            if !log_all_flag then begin
                output_string log_all ("#gist" ^ Util.new_line_str ^ Util.new_line_str);
                output_string log_all ((Util.break_lines fomega) ^ Util.new_line_str ^ Util.new_line_str);
                flush log_all;
            end;
    let rel = send_and_receive fomega 0. in
	  match_vars vars_list rel
  end

let log_mark (mark : string) =
  if !log_all_flag then begin
    output_string log_all ("#mark: " ^ mark ^ Util.new_line_str ^ Util.new_line_str);
    flush log_all;
  end;

