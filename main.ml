(******************************************)
(* command line processing                *)
(******************************************)

let to_java = ref false

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let set_source_file arg = 
  Globals.source_files := arg :: !Globals.source_files

let process_cmd_line () = Arg.parse Scriptarguments.hip_arguments set_source_file usage_msg

(******************************************)
(* main function                          *)
(******************************************)

let exe_url = Sys.argv.(0)

let get_exe_direct_link ()  =
  try
     let name_index = String.rindex exe_url '/' in
     try
        String.sub exe_url 0 (name_index+1)
     with Invalid_argument "" -> "./"
  with Not_found -> "./"

let parse_file_full file_name = 
  let org_in_chnl = open_in file_name in
  let input = Lexing.from_channel org_in_chnl in
    try
    (*let ptime1 = Unix.times () in
	  let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in
     *)
		print_string "Parsing...\n"; flush stdout;
        let _ = Util.push_time "Parsing" in
    Iparser.file_name := file_name;
		let prog = Iparser.program (Ilexer.tokenizer file_name) input in
		  close_in org_in_chnl;
         let _ = Util.pop_time "Parsing" in
    (*		  let ptime2 = Unix.times () in
		  let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
			print_string ("done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n"); *)
			prog 
    with
		End_of_file -> exit 0	  

(* Parse all prelude files declared by user.*)
let rec process_primitives file_list =
  match file_list with
  | [] -> []
  | hd::tl ->
        let header_filename = String.sub hd 1 ((String.length hd) - 2) in
        (*let sleekex_link = get_exe_direct_link() in*)
        let sleekex_link = "/home/an/sleekex/" in
        let new_filename = sleekex_link ^ header_filename in
        let primitives = parse_file_full new_filename in
                primitives :: (process_primitives tl)

(* Process all intermediate primitives which receive after parsing *)
let rec process_intermediate_prims prims_list =
  match prims_list with
  | [] -> []
  | hd::tl ->
        let iprims = Globalvars.trans_global_to_param hd in
        let iprims = Iast.label_procs_prog iprims in
                iprims :: (process_intermediate_prims tl)

(* Process prelude pragma *)
let rec process_header_with_pragma hlist plist =
  match plist with
  | [] -> hlist
  | hd::tl ->
        let new_hlist = if (hd = "NoImplicitPrelude") then [] else hlist in
            process_header_with_pragma new_hlist tl

let process_source_full source =
  print_string ("\nProcessing file \"" ^ source ^ "\"\n"); flush stdout;
  let _ = Util.push_time "Preprocessing" in
  let prog = parse_file_full source in
  let header_files = Util.remove_dups !Globals.header_file_list in (* Remove all duplicated declared prelude *)
  let new_h_files = process_header_with_pragma header_files !Globals.pragma_list in
  let prims_list = process_primitives new_h_files in
  	if !to_java then begin
	  print_string ("Converting to Java..."); flush stdout;
	  let tmp = Filename.chop_extension (Filename.basename source) in
	  let main_class = Util.replace_minus_with_uscore tmp in
	  let java_str = Java.convert_to_java prog main_class in
	  let tmp2 = Util.replace_minus_with_uscore (Filename.chop_extension source) in
	  let jfile = open_out ("output/" ^ tmp2 ^ ".java") in
		output_string jfile java_str;
		close_out jfile;
		print_string (" done.\n"); flush stdout;
		exit 0
	end;
  	if (!Scriptarguments.parse_only) then 
      let _ = Util.pop_time "Preprocessing" in
      print_string (Iprinter.string_of_program prog)
	else 
      let _ = Tpdispatcher.start_prover () in
	  (* Global variables translating *)
      let _ = Util.push_time "Translating global var" in
   	  let _ = print_string ("Translating global variables to procedure parameters...\n"); flush stdout in
          (* Append all primitives in list into one only *)
          let iprims_list = process_intermediate_prims prims_list in
          let iprims = Iast.append_iprims_list_head iprims_list in 
          let intermediate_prog = Globalvars.trans_global_to_param prog in
	  let intermediate_prog = Iast.label_procs_prog intermediate_prog in
		Cprinter.iprog := intermediate_prog;
	  let _ = if (!Globals.print_input) then print_string (Iprinter.string_of_program intermediate_prog) else () in
      let _ = Util.pop_time "Translating global var" in
	  (* Global variables translated *)
	  (* let ptime1 = Unix.times () in
	  let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in *)
      let _ = Util.push_time "Translating to Core" in
	  let _ = print_string ("Translating to core language..."); flush stdout in
          (* Append primitives to main program and convert from iast to cast *)
	  let cprog = Astsimp.trans_prog intermediate_prog iprims in
	  let _ = print_string (" done\n"); flush stdout in
	  let _ = if (!Globals.print_core) then print_string (Cprinter.string_of_program cprog) else () in
	  let _ = 
		if !Globals.verify_callees then begin
		  let tmp = Cast.procs_to_verify cprog !Globals.procs_verified in
			Globals.procs_verified := tmp
		end in
      let _ = Util.pop_time "Translating to Core" in
	  (* let ptime2 = Unix.times () in
	  let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
	  let _ = print_string (" done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n") in *)
	  let _ =
		if !Scriptarguments.comp_pred then begin
		  let _ = print_string ("Compiling predicates to Java..."); flush stdout in
		  let compile_one_view vdef = 
			if (!Scriptarguments.pred_to_compile = ["all"] || List.mem vdef.Cast.view_name !Scriptarguments.pred_to_compile) then
			  let data_def, pbvars = Predcomp.gen_view cprog vdef in
			  let java_str = Java.java_of_data data_def pbvars in
			  let jfile = open_out (vdef.Cast.view_name ^ ".java") in
				print_string ("\n\tWriting Java file " ^ vdef.Cast.view_name ^ ".java");
				output_string jfile java_str;
				close_out jfile
			else
			  ()
		  in
			ignore (List.map compile_one_view cprog.Cast.prog_view_decls);
			print_string ("\nDone.\n"); flush stdout;
			exit 0
		end 
	  in
	  let _ =
		if !Scriptarguments.rtc then begin
		  Rtc.compile_prog cprog source;
		  exit 0
		end
	  in
	    let _ = Util.pop_time "Preprocessing" in
		ignore (Typechecker.check_prog cprog);
		(* Stopping the prover *)
		let _ = Tpdispatcher.stop_prover () in
		
		let ptime4 = Unix.times () in
		let t4 = ptime4.Unix.tms_utime +. ptime4.Unix.tms_cutime +. ptime4.Unix.tms_stime +. ptime4.Unix.tms_cstime   in
		print_string ("\n"^(string_of_int (List.length !Globals.false_ctx_line_list))^" false contexts at: ("^
		(List.fold_left (fun a c-> a^" ("^(string_of_int c.Globals.start_pos.Lexing.pos_lnum)^","^
		( string_of_int (c.Globals.start_pos.Lexing.pos_cnum-c.Globals.start_pos.Lexing.pos_bol))^") ") "" !Globals.false_ctx_line_list)^")\n");
		  print_string ("\nTotal verification time: " 
				^ (string_of_float t4) ^ " second(s)\n"
				^ "\tTime spent in main process: " 
				^ (string_of_float (ptime4.Unix.tms_utime+.ptime4.Unix.tms_stime)) ^ " second(s)\n"
				^ "\tTime spent in child processes: " 
				^ (string_of_float (ptime4.Unix.tms_cutime +. ptime4.Unix.tms_cstime)) ^ " second(s)\n")
	  
let main1 () =
  (* Cprinter.fmt_set_margin 40; *)
  (* Cprinter.fmt_string "TEST1.................................."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST2...............................................................'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''............"; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST3....."; *)
  (*  Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST3....."; *)
  (*  Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST3....."; *)
  (*    Cprinter.fmt_string "TEST3....."; *)
  (* Cprinter.fmt_string "TEST4..............................."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST5.................................."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST6.................................."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST7.................................."; *)
  (*  Cprinter.fmt_cut (); *)
  process_cmd_line ();
  
    if List.length (!Globals.source_files) = 0 then begin
      (* print_string (Sys.argv.(0) ^ " -help for usage information\n") *)
      Globals.procs_verified := ["f3"];
      Globals.source_files := ["examples/test5.ss"]
    end;
    let _ = Util.push_time "Overall" in
    let _ = List.map process_source_full !Globals.source_files in
    let _ = Util.pop_time "Overall" in
      (* Tpdispatcher.print_stats (); *)
      ()
	  
let _ = 
  main1 ();
  let _ = print_string (Util.string_of_counters ()) in
  let _ = Util.print_profiling_info () in
  ()


  
