open Globals 
open Gen.Basic
open Printf

module CP = Cpure

type proof_type = 
	| IMPLY of (CP.formula * CP.formula)
	| SAT of CP.formula
	| SIMPLIFY of CP.formula

type proof_res =
	| BOOL of bool
	| FORMULA of CP.formula

type proof_log = {
	log_id : string; (* TODO: Should change to integer for performance *)
	log_old_id : string; (* TODO: Should change to integer for performance *)
	log_prover : string;
	log_type : proof_type option;
	log_time : float;
	log_res : proof_res;
}

let proof_log_tbl : (string, proof_log) Hashtbl.t = Hashtbl.create 700

let proof_log_list  = ref [] (*For printing to text file with the original oder of proof execution*)

(*TO DO: check unique pno??*)
let add_proof_log old_no pno tp ptype time res =
	if !Globals.proof_logging || !Globals.proof_logging_txt then
		let tstartlog = Gen.Profiling.get_time () in
		let plog = {
			log_id = pno;
			log_old_id = proving_info ();
			(* log_old_id = old_no; *)
			log_prover = tp;
			log_type = Some ptype;
			log_time = time;
			log_res = res; } in
		let _=Hashtbl.add proof_log_tbl pno plog in
		let _= if(!Globals.proof_logging_txt) then
			begin 
			proof_log_list := !proof_log_list @ [pno];
			end		
		in
	let tstoplog = Gen.Profiling.get_time () in
	let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in ()
	(* let _=print_endline ("log time: "^(string_of_float (tstoplog))^" and "^(string_of_float (tstartlog))) in ()	  *)
	else ()
	
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


	(* let oc =                                                                                                                                                   *)
	(* 	(try Unix.mkdir "logs" 0o750 with _ -> ());                                                                                                              *)
	(* 	 open_out_gen [Open_creat; Open_text; Open_append] 0o640  ("logs/bach_proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files)) ^".txt") in *)
	(* 			let _=fprintf oc "%s" (sat_no^"let is_sat\n") in                                                                                                     *)
	(* 	close_out oc;	                                                                                                                                          *)
		
