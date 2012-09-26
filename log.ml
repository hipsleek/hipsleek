open Globals 
open Gen.Basic

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
	log_prover : string;
	log_type : proof_type option;
	log_time : float;
	log_res : proof_res;
}

let proof_log_tbl : (string, proof_log) Hashtbl.t = Hashtbl.create 200

let add_proof_log pno tp ptype time res =
	if !Globals.proof_logging then
		let plog = {
			log_id = pno;
			log_prover = tp;
			log_type = Some ptype;
			log_time = time;
			log_res = res; } in
		Hashtbl.add proof_log_tbl pno plog
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
