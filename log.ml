open Globals 
open Stat_global
open Gen.Basic
open Printf
open Cprinter

module CP = Cpure
module CF = Cformula

type proof_type = 
	| IMPLY of (CP.formula * CP.formula)
	| SAT of CP.formula
	| SIMPLIFY of CP.formula

type proof_res =
	| BOOL of bool
	| FORMULA of CP.formula

type proof_log = {
	log_id : string; (* TODO: Should change to integer for performance *)
	log_other_properties : string list; (* TODO: Should change to integer for performance *)
	log_prover : string;
	log_type : proof_type option;
	log_time : float;
	log_res : proof_res;
}

let sleek_counter= ref 0

let proof_log_tbl : (string, proof_log) Hashtbl.t = Hashtbl.create 700

let proof_log_list  = ref [] (*For printing to text file with the original oder of proof execution*)

let proof_gt5_log_list = ref [] (*Logging proofs require more than 5 secs to be proved*)
		
let find_bool_proof_res pno =
	try 
		let log = Hashtbl.find proof_log_tbl pno in
		match log.log_res with
		| BOOL r -> r
		| _ -> report_error no_pos "Fatal error with Proof Logging: Unexpected result."
	with _ -> report_error no_pos "Fatal error with Proof Logging. Do remember to enable proof logging before using LOG."

let find_formula_proof_res pno =
	try 
		let log = Hashtbl.find proof_log_tbl pno in
		match log.log_res with
		| FORMULA r -> r
		| _ -> report_error no_pos "Fatal error with Proof Logging: Unexpected result."
	with _ -> report_error no_pos "Fatal error with Proof Logging. Do remember to enable proof logging before using LOG."	
			
let proof_log_to_file () = 
	let out_chn = 
		(try Unix.mkdir "logs" 0o750 with _ -> ());
		open_out ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files))) in
	 output_value out_chn proof_log_tbl 
	
let file_to_proof_log () =
	try 
		let in_chn = open_in ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files))) in
		let tbl = input_value in_chn in
		Hashtbl.iter (fun k log -> Hashtbl.add proof_log_tbl k log) tbl
	with _ -> report_error no_pos "File of proof logging cannot be opened."

(* let log_append_properties (ls: string ) = (\*For append more properties to log, currently not used*\) *)
(* 	try *)
(* 	 let tl= List.nth !proof_log_list ((List.length !proof_log_list) -1) in *)
(* 	 let tlog=Hashtbl.find proof_log_tbl tl in *)
(* 	 let _= tlog.log_other_properties <- tlog.log_other_properties @ [ls] in *)
(* 	 print_endline (ls) *)
(*   with _-> () *)
	
(*TO DO: check unique pno??*)
let add_proof_log old_no pno tp ptype time res =
  if !Globals.proof_logging || !Globals.proof_logging_txt then
	(* let _= print_endline ("loging :"^pno^" "^proving_info () ^"\n"^trace_info ()) in *)
	let tstartlog = Gen.Profiling.get_time () in
	let plog = {
		log_id = pno;
		log_other_properties = [proving_info ()]@[trace_info ()];
		(* log_old_id = old_no; *)
		log_prover = tp;
		log_type = Some ptype;
		log_time = time;
		log_res = res; } in
	let _=Hashtbl.add proof_log_tbl pno plog in
	let _=try
	  let _= BatString.find (Sys.argv.(0)) "hip" in
	  if(!Globals.proof_logging_txt && ((proving_kind # string_of)<>"TRANS_PROC")) then
		begin 
		  proof_log_list := !proof_log_list @ [pno];
		end		
	with _->
		if(!Globals.proof_logging_txt) then
		  try
			let temp=(proving_kind # string_of) in
			let _ =
              if !Globals.log_filter
              then BatString.find temp "SLEEK_ENT"
              else 0 in
			begin 
			  proof_log_list := !proof_log_list @ [pno];
			end		 	
		  with _->()	
	in
	let tstoplog = Gen.Profiling.get_time () in
	let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in ()
	                                                                                                   (* let _=print_endline ("log time: "^(string_of_float (tstoplog))^" and "^(string_of_float (tstartlog))) in ()	  *)
  else ()
					
let proof_log_to_text_file (src_files) =
  if !Globals.proof_logging_txt then
    let tstartlog = Gen.Profiling.get_time () in
    let oc = 
      (try Unix.mkdir "logs" 0o750 with _ -> ());
      let with_option = if !Globals.en_slc_ps then "eps" else "no_eps" in
      open_out ("logs/"^with_option^"_proof_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt") in
    let string_of_log_type lt =
      match lt with
	|IMPLY (ante, conseq) -> "Imply: ante:" ^(string_of_pure_formula ante) ^"\n\t     conseq: " ^(string_of_pure_formula conseq)
    	|SAT f-> "Sat: "^(string_of_pure_formula f) 
    	|SIMPLIFY f -> "Simplify: "^(string_of_pure_formula f)
    in
    let helper log=
      "\n--------------\n"^
	  List.fold_left (fun a c->a^c) "" log.log_other_properties^
	  (* "\nid: "^log.log_id^ *)
      "\nProver: "^log.log_prover^"\nType: "^(match log.log_type with | Some x-> string_of_log_type x | None -> "????")^
      (* "\nTime: "^(string_of_float(log.log_time))^ *)
      "\nResult: "^(match log.log_res with
	    |BOOL b -> string_of_bool b
	    |FORMULA f -> string_of_pure_formula f)^"\n" in
    let _= List.map (fun ix->let log=Hashtbl.find proof_log_tbl ix in
    let _=fprintf oc "%s" (helper log) in ()) !proof_log_list in
    let tstoplog = Gen.Profiling.get_time () in
    let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in 
    close_out oc;
  else ()	

let z3_proofs_list_to_file (src_files) =
	if !Globals.proof_logging_txt then
		let tstartlog = Gen.Profiling.get_time () in
		let oc = 
		(try Unix.mkdir "logs" 0o750 with _ -> ());
		(* let with_option= if(!Globals.do_slicing) then "slice" else "noslice" in *)
		let with_option = if(!Globals.en_slc_ps) then "eps" else "no_eps" in
		let with_option= with_option^"_"^if(!Globals.split_rhs_flag) then "rhs" else "norhs" in
    let with_option= with_option^"_"^if(not !Globals.elim_exists) then "noee" else "ee" in
		open_out ("logs/"^with_option^"_"^(Globals.norm_file_name (List.hd src_files)) ^".z3") in
		let _= List.map (fun ix-> let _=fprintf oc "%s" ix in ()) !z3_proof_log_list in
		let tstoplog = Gen.Profiling.get_time () in
	  let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in 
		close_out oc;
	else ()	

let proof_greater_5secs_to_file (src_files) =
	if !Globals.proof_logging_txt then
		let tstartlog = Gen.Profiling.get_time () in
		let oc = 
		(try Unix.mkdir "logs" 0o750 with _ -> ());
		(* let with_option= if(!Globals.do_slicing) then "slice" else "noslice" in *)
		let with_option = if(!Globals.en_slc_ps) then "eps" else "no_eps" in
		let with_option= with_option^"_"^if(!Globals.split_rhs_flag) then "rhs" else "norhs" in
    let with_option= with_option^"_"^if(not !Globals.elim_exists) then "noee" else "ee" in
		open_out ("logs/greater_5sec_"^with_option^"_"^(Globals.norm_file_name (List.hd src_files)) ^".log5") in
		let _= List.map (fun ix-> let _=fprintf oc "%s" ix in ()) !proof_gt5_log_list in
		let tstoplog = Gen.Profiling.get_time () in
	  let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in 
		close_out oc;
	else ()	

let wrap_calculate_time exec_func src_file args =
  (* if !Globals.proof_logging_txt then  *)
	  let _= sleek_counter := !sleek_counter +1 in
		let tstartlog = Gen.Profiling.get_time () in
    let _ = exec_func args in
		let tstoplog = Gen.Profiling.get_time () in 
		let period = (tstoplog -. tstartlog) in
	  if (period> 0.7) then
			proof_gt5_log_list :=  
			(!proof_gt5_log_list@[(Globals.norm_file_name (List.hd src_file))^"-check-entail-num-"^string_of_int !sleek_counter^"--Time--"^string_of_float (period)^"\n"])
  (* else exec_func args *)
	
(* let sleek_z3_proofs_list_to_file source_files =                                                    *)
(* 	if !Globals.proof_logging_txt then                                                               *)
(* 		let tstartlog = Gen.Profiling.get_time () in                                                   *)
(* 		let oc =                                                                                       *)
(* 		(try Unix.mkdir "logs" 0o750 with _ -> ());                                                    *)
(* 		let with_option= if(!Globals.do_slicing) then "sleek_slice" else "sleek_noslice" in            *)
(* 		(* let with_option= with_option^"_"^if(!Globals.split_rhs_flag) then "rhs" else "norhs" in *)  *)
(* 		open_out ("logs/"^with_option^(Globals.norm_file_name (List.hd source_files)) ^".z3") in       *)
(* 		let _= List.map (fun ix-> let _=fprintf oc "%s" ix in ()) !z3_proof_log_list in                *)
(* 		let tstoplog = Gen.Profiling.get_time () in                                                    *)
(* 	  let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in *)
(* 		close_out oc;                                                                                  *)
(* 	else ()                                                                                          *)
		
