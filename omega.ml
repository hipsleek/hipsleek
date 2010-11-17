(*
  Call Omega Calculator, send input to it
*)

open Globals
open Cpure


let infilename = ref ("input.oc." ^ (string_of_int (Unix.getpid ())))
let resultfilename = ref ("result.txt." ^ (string_of_int (Unix.getpid())))

let init_files () =
  begin
	infilename := "input.oc." ^ (string_of_int (Unix.getpid ()));
	resultfilename := "result.txt." ^ (string_of_int (Unix.getpid()));
  end

let test_number = ref 0
let log_all_flag = ref false
let log_all = open_out ("allinput.oc" (* ^ (string_of_int (Unix.getpid ())) *) )

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

let omega_calc_command =
  if Sys.os_type = "Cygwin" then ("dos2unix " ^ !infilename ^ " ; " ^ omegacalc ^ " " ^ !infilename ^ " > " ^ !resultfilename)
  else (omegacalc ^ " " ^ !infilename ^ " > " ^ !resultfilename)

let set_timer tsecs =
  ignore (Unix.setitimer Unix.ITIMER_REAL
            { Unix.it_interval = 0.0; Unix.it_value = tsecs })

(*let continue f arg tsecs pid =
  let oldsig = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Exit)) in
  try
    set_timer tsecs;
    ignore (f arg);
    set_timer 0.0;
    Sys.set_signal Sys.sigalrm oldsig; true
  with Exit ->
    Sys.set_signal Sys.sigalrm oldsig; false
(*  begin continue Sys.command omega_calc_command timeout end*)
	*)

let run_omega (input : string) (timeout : float):bool = begin
	let chn = open_out !infilename in
	output_string chn (Util.break_lines input);
    close_out chn;
    (* flush_all(); *)
 	let pid = Unix_add.open_proc omegacalc [|omegacalc;!infilename|] !resultfilename in
	let oldsig = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Exit)) in	
	let r =	try 			
			begin
			set_timer timeout;
			ignore (Unix.waitpid [] pid);
			true end
		with Exit ->
			begin
			print_endline "\nOmega timeout reached."; flush stdout; 
			Unix.kill pid 9;
			ignore (Unix.waitpid [] pid);
			false end in
	set_timer 0.0;
	Sys.set_signal Sys.sigalrm oldsig;
	r end

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
    if !log_all_flag then begin
(*      output_string log_all ("YYY" ^ (Cprinter.string_of_pure_formula pe) ^ "\n");*)
      output_string log_all (Util.new_line_str^"#is_sat " ^ sat_no ^ Util.new_line_str);
      output_string log_all (Util.break_lines fomega);
      flush log_all;
    end;
    let quitloop = ref false in
    let sat = ref true in
    if (run_omega fomega !Globals.sat_timeout = false) then (quitloop := true);
    let chn = open_in !resultfilename in
    while not !quitloop do
      let line = input_line chn in
      let n = String.length line in
      if n > 0 then begin
        (if !log_all_flag then 
          output_string log_all ("[omega.ml]: >> "^line^"\n") );
        if line.[0] != '#' then begin
          quitloop := true;
          if n > 7 then
            let lastchars = String.sub line (n - 7) 7 in
            if lastchars = "FALSE }" then
              sat := false
        end;
      end;
    done;
    close_in chn;
    begin
      try
        ignore (Sys.remove !infilename);
        ignore (Sys.remove !resultfilename)
      with
      | e -> ignore e
    end;
    if !log_all_flag = true then begin
      if !sat then output_string log_all ("[omega.ml]: unsat "^sat_no ^(string_of_int !test_number)^" --> FAIL\n") else output_string log_all ("[omega.ml]: unsat "^sat_no^(string_of_int !test_number)^" --> SUCCESS\n");
    end else ();
    !sat
  end

(*
    let is_valid (pe : pConstr) : bool =
  begin
  let fstr = omega_of_formula pe in
  let vstr = omega_of_var_list (Util.remove_dups (get_vars_pConstr pe)) in
  let truestr = "{[" ^ vstr ^ "] : 0 = 0 }" in
  let fomega =  truestr ^ " subset {[" ^ vstr ^ "] : (" ^ fstr ^ ")}" ^ ";\n" in
    output_string log_all ("#is_valid\n\n");
    output_string log_all ((Util.break_lines fomega) ^ "\n\n");
    flush log_all;
  run_omega fomega;
  let chn = open_in resultfilename in
  let quitloop = ref false in
  let result = ref false in
    while not !quitloop do
    let line = input_line chn in
    if String.length line > 0 then
    if line.[0] != '#' then
    begin
    quitloop := true;
    if line = "True" || line = "{ TRUE }" then
    result := true
    else if line = "False" || line = "{ FALSE }" then
    result := false
    end;
    done;
    !result
  end
*)

let is_valid (pe : formula) timeout: bool =
  begin
		Ocparser.subst_lst := [];
    let fstr = omega_of_formula pe in
    let vstr = omega_of_var_list (Util.remove_dups (get_vars_formula pe)) in
    let fomega =  "complement {[" ^ vstr ^ "] : (" ^ fstr ^ ")}" ^ ";" ^ Util.new_line_str in
            if !log_all_flag then begin
(*                output_string log_all ("YYY" ^ (Cprinter.string_of_pure_formula pe) ^ "\n");*)
                output_string log_all (Util.new_line_str^"#is_valid" ^Util.new_line_str);
                output_string log_all (Util.break_lines fomega);
                flush log_all;
            end;
      let quitloop = ref false in
      let result = ref false in
      if not (run_omega fomega timeout) then (quitloop:=true) ;
      (*ignore (run_omega fomega timeout);*)
      let chn = open_in !resultfilename in      
                while not !quitloop do
                    let line = input_line chn in
                    let n = String.length line in
                       (if !log_all_flag then 
                          output_string log_all ("[omega.ml]: >> "^line^"\n") );
                        if n > 0 then begin
                            if line.[0] != '#' then begin
                                quitloop := true;
                                if n > 7 then
                                    let lastchars = String.sub line (n - 7) 7 in
                                        if lastchars = "FALSE }" then
                                            result := true
                            end;
                        end;
                done;
                close_in chn;
                begin
                    try
                        ignore (Sys.remove !infilename);
                        ignore (Sys.remove !resultfilename)
                    with
                        | e -> ignore e
                end;
                !result
  end

let imply (ante : formula) (conseq : formula) (imp_no : string) timeout : bool =
  incr test_number;
  (*
    let tmp1 = mkAnd ante (mkNot conseq no_pos) no_pos in
    let fvars = fv tmp1 in
    let tmp2 = mkExists fvars tmp1 no_pos in
    not (is_valid tmp2)
   *)
  let tmp_form = mkOr (mkNot ante None no_pos) conseq None no_pos in
  let result = is_valid tmp_form timeout in
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
  begin
    Ocparser.subst_lst := [];
    let fstr = omega_of_formula pe in
    let vars_list = get_vars_formula pe in
    let vstr = omega_of_var_list (Util.remove_dups vars_list) in
    let fomega =  "{[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Util.new_line_str in
    if !log_all_flag then begin
(*                output_string log_all ("YYY" ^ (Cprinter.string_of_pure_formula pe) ^ "\n");*)
      output_string log_all ("#simplify" ^ Util.new_line_str ^ Util.new_line_str);
      output_string log_all ((Util.break_lines fomega) ^ Util.new_line_str ^ Util.new_line_str);
      flush log_all;
    end;
    let r = run_omega fomega 0. in
    let chn = open_in !resultfilename in
    let f = if r then 
      let lex_buf = Lexing.from_channel chn in
      let rel = Ocparser.oc_output (Oclexer.tokenizer !resultfilename) lex_buf in
       match_vars (fv pe) rel 
      else pe in
      begin
        try
          ignore (Sys.remove !infilename);
          ignore (Sys.remove !resultfilename)
        with
        | e -> ignore e
      end;
      close_in chn;
      f
  end

let pairwisecheck (pe : formula) : formula =
  begin
		Ocparser.subst_lst := [];
    let fstr = omega_of_formula pe in
        let vars_list = get_vars_formula pe in
    let vstr = omega_of_var_list (Util.remove_dups vars_list) in
    let fomega =  "pairwisecheck {[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Util.new_line_str in
            if !log_all_flag then begin
                output_string log_all ("#pairwisecheck" ^ Util.new_line_str ^ Util.new_line_str);
                output_string log_all ((Util.break_lines fomega) ^ Util.new_line_str ^ Util.new_line_str);
                flush log_all;
            end;
      (*ignore (run_omega fomega 0.);*)
    let r = run_omega fomega 0. in
    let chn = open_in !resultfilename in
    let f = if r then 
      let lex_buf = Lexing.from_channel chn in
      let rel = Ocparser.oc_output (Oclexer.tokenizer !resultfilename) lex_buf in
      match_vars (fv pe) rel 
      else pe in
    begin
      try
        ignore (Sys.remove !infilename);
        ignore (Sys.remove !resultfilename)
      with
        | e -> ignore e
    end;
    close_in chn;
    f
  end

let hull (pe : formula) : formula =
  begin
		Ocparser.subst_lst := [];
    let fstr = omega_of_formula pe in
        let vars_list = get_vars_formula pe in
    let vstr = omega_of_var_list (Util.remove_dups vars_list) in
    let fomega =  "hull {[" ^ vstr ^ "] : (" ^ fstr ^ ")};" ^ Util.new_line_str in
            if !log_all_flag then begin
                output_string log_all ("#hull" ^ Util.new_line_str ^ Util.new_line_str);
                output_string log_all ((Util.break_lines fomega) ^ Util.new_line_str ^ Util.new_line_str);
                flush log_all;
            end;
      (*ignore (run_omega fomega 0.);*)
      let r = run_omega fomega 0. in
      let chn = open_in !resultfilename in
      let f = if r then 
        let lex_buf = Lexing.from_channel chn in
        let rel = Ocparser.oc_output (Oclexer.tokenizer !resultfilename) lex_buf in
        match_vars (fv pe) rel 
        else pe in
      begin
        try
          ignore (Sys.remove !infilename);
          ignore (Sys.remove !resultfilename)
        with
          | e -> ignore e
      end;
      close_in chn;
      f
  end
(*
let gist (pe1 : formula) (pe2 : formula) : formula =
  begin
		Ocparser.subst_lst := [];
    let fstr1 = omega_of_formula pe1 in
        let fstr2 = omega_of_formula pe2 in
        let vars_list = Util.remove_dups_f (fv pe1 @ fv pe2)  eq_spec_var  in
				let l1 = List.map omega_of_spec_var vars_list  in
    let vstr = String.concat ", " l1  in
    let fomega =  "gist {[" ^ vstr ^ "] : (" ^ fstr1
            ^ ")} given {[" ^ vstr ^ "] : (" ^ fstr2 ^ ")};" ^ Util.new_line_str
        in
            if !log_all_flag then begin
                output_string log_all ("#gist" ^ Util.new_line_str ^ Util.new_line_str);
                output_string log_all ((Util.break_lines fomega) ^ Util.new_line_str ^ Util.new_line_str);
                flush log_all;
            end;
      if (run_omega fomega 0.) then 
            let chn = open_in !resultfilename in
            let lex_buf = Lexing.from_channel chn in
            let rel = Ocparser.oc_output (Oclexer.tokenizer !resultfilename) lex_buf in
            let f = match_vars vars_list rel in
                begin
                    try
                        ignore (Sys.remove !infilename);
                        ignore (Sys.remove !resultfilename)
                    with
                        | e -> ignore e
                end;
                close_in chn;
                f
      else 
  end
*)
let log_mark (mark : string) =
  if !log_all_flag then begin
    output_string log_all ("#mark: " ^ mark ^ Util.new_line_str ^ Util.new_line_str);
    flush log_all;
  end;

