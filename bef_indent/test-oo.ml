#include "xdebug.cppo"
(******************************************)
(* command line processing                *)
(******************************************)

let parse_only = ref false

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let set_source_file arg = 
  Globals.source_files := arg :: !Globals.source_files

let set_proc_verified arg =
  let procs = Gen.split_by "," arg in
	Globals.procs_verified := procs @ !Globals.procs_verified
	
let process_cmd_line () = Arg.parse [
  ("--verify-callees", Arg.Set Globals.verify_callees,
   "Verify callees of the specified procedures");
  ("-dd", Arg.Set Debug.devel_debug_on,
   "Turn on devel_debug");
  ("--hull-pre-inv", Arg.Set Globals.hull_pre_inv,
   "Hull precondition invariant at call sites");
(*
  ("--log-cvcl", Arg.String Cvclite.set_log_file,
   "Log all CVC Lite formula to specified log file");
  ("--log-omega", Arg.Set Omega.log_all_flag,
   "Log all formulae sent to Omega Calculator in file allinput.oc");
  ("--log-isabelle", Arg.Set Isabelle.log_all_flag,
   "Log all formulae sent to Isabelle in file allinput.thy");
  ("--log-mona", Arg.Set Mona.log_all_flag,
   "Log all formulae sent to Mona in file allinput.mona");
  ("--use-isabelle-bag", Arg.Set Isabelle.bag_flag,
   "Use the bag theory from Isabelle, instead of the set theory");
*)
  ("--no-coercion", Arg.Clear Globals.use_coercion,
   "Turn off coercion mechanism");
  ("--no-exists-elim", Arg.Clear Globals.elim_exists,
   "Turn off existential quantifier elimination during type-checking");
  ("--no-set", Arg.Clear Globals.use_set,
   "Turn of set-of-states search");
  ("--no-unsat-elim", Arg.Clear Globals.elim_unsat,
   "Turn off unsatisfiable formulae elimination during type-checking");
  ("-nxpure", Arg.Set_int Globals.n_xpure,
   "Number of unfolding using XPure");
  ("-p", Arg.String set_proc_verified, 
   "Procedure to be verified. If none specified, all are verified.");
  ("-parse", Arg.Set parse_only,
   "Parse only");
  ("-print", Arg.Set Globals.print_proc,
   "Print procedures being checked");
  ("--print-x-inv", Arg.Set Globals.print_x_inv,
   "Print computed view invariants");
  ("-stop", Arg.Clear Globals.check_all,
   "Stop checking on erroneous procedure");
(*
  ("--build-image", Arg.Symbol (["true"; "false"], Isabelle.building_image),
   "Build the image theory in Isabelle - default false");
  ("-tp", Arg.Symbol (["cvcl"; "omega"; "co"; "isabelle"; "mona"], Tpdispatcher.set_tp),
   "Choose theorem prover:\n\tcvcl: CVC Lite\n\tomega: Omega Calculator (default)\n\tco: CVC Lite then Omega");
*)
  ("--use-field", Arg.Set Globals.use_field,
   "Use field construct instead of bind");
  ("--use-large-bind", Arg.Set Globals.large_bind,
   "Use large bind construct, where the bound variable may be changed in the body of bind");
  ("-v", Arg.Set Debug.debug_on, 
   "Verbose")] set_source_file usage_msg

(******************************************)
(* main function                          *)
(******************************************)

let parse_file_full file_name = 
  let org_in_chnl = open_in file_name in
  let input = Lexing.from_channel org_in_chnl in
    try
	  let ptime1 = Unix.times () in
	  let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in
		print_string "Parsing... ";
		let prog = Iparser.program (Ilexer.tokenizer file_name) input in
		  close_in org_in_chnl;
		  let ptime2 = Unix.times () in
		  let t2 = ptime1.Unix.tms_utime +. ptime2.Unix.tms_cutime in
			print_string ("done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n");
			prog
    with
		End_of_file -> exit 0	  

let process_source_full source =
  print_string ("\nProcessing file \"" ^ source ^ "\"\n");
  let prog = parse_file_full source in
  let pstr = Iprinter.string_of_program prog in
	print_string ("Orignial program:\n\n" ^ pstr ^ "\n");
	if not (!parse_only) then
	  let ptime1 = Unix.times () in
	  let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in
	  let () = print_string ("Translating to core language...") in
	  (* let cprog = Astsimp.trans_prog prog in *)
		let cprog = Astsimp.trans_prog prog in
	  let pstr2 = Cprinter.string_of_program cprog in
		print_string ("Core program:\n\n" ^ pstr2 ^ "\n")		
(*
	  let () = 
		if !Globals.verify_callees then begin
		  let tmp = Cast.procs_to_verify cprog !Globals.procs_verified in
			Globals.procs_verified := tmp
		end in
	  let ptime2 = Unix.times () in
	  let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
	  let () = print_string (" done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n") in
		ignore (Typechecker.check_prog cprog);
		let ptime4 = Unix.times () in
		let t4 = ptime4.Unix.tms_utime +. ptime4.Unix.tms_cutime in
		  print_string ("\nTotal verification time: " ^ (string_of_float t4) ^ " second(s)\n"
						^ "\tTime spent in main process: " ^ (string_of_float ptime4.Unix.tms_utime) ^ " second(s)\n"
						^ "\tTime spent in child processes: " ^ (string_of_float ptime4.Unix.tms_cutime) ^ " second(s)\n")
*)
	  
let main () =
  process_cmd_line ();
  let () = Debug.read_main () in
  if List.length (!Globals.source_files) = 0 then begin
	(* print_string (Sys.argv.(0) ^ " -help for usage information\n") *)
	Globals.procs_verified := ["f3"];
	Globals.source_files := ["examples/test5.ss"]
  end;
  let todo_unk = List.map process_source_full !Globals.source_files in
	(* Tpdispatcher.print_stats (); *)
	()
	  
let () = main ()
