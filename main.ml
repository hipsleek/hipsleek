(* test - added to immutability branch *)
(******************************************)
(* command line processing                *)
(******************************************)
open Gen.Basic

module M = Lexer.Make(Token.Token)

let to_java = ref false

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let set_source_file arg = 
  Globals.source_files := arg :: !Globals.source_files

let process_cmd_line () = Arg.parse Scriptarguments.hip_arguments set_source_file usage_msg

let print_version () =
  print_endline ("HIP: A Verifier for Heap Manipulating Programs");
  print_endline ("Version 1.0");
  print_endline ("THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.");
  print_endline ("IT IS FREE FOR NON-COMMERCIAL USE");
  print_endline ("Copyright @ PLS2 @ NUS")

(******************************************)
(* main function                          *)
(******************************************)

let parse_file_full file_name = 
  let org_in_chnl = open_in file_name in
    try
    (*let ptime1 = Unix.times () in
	  let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in
     *)
      (* print_string ("Parsing "^file_name^" ...\n"); flush stdout; *)
      let _ = Gen.Profiling.push_time "Parsing" in
      Globals.input_file_name:= file_name;
      let prog = Parser.parse_hip file_name (Stream.of_channel org_in_chnl) in
		  close_in org_in_chnl;
         let _ = Gen.Profiling.pop_time "Parsing" in
    (*		  let ptime2 = Unix.times () in
		  let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
			print_string ("done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n"); *)
		(* An Hoa *)
		(*let _ = print_endline "Primitive relations : " in
		let _ = List.map (fun x -> print_endline x.Iast.rel_name) prog.Iast.prog_rel_decls in*)

			prog
    with
		End_of_file -> exit 0
    | M.Loc.Exc_located (l,t)->
      (print_string ((Camlp4.PreCast.Loc.to_string l)^"\n --error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
      raise t)

(* Parse all prelude files declared by user.*)
let process_primitives (file_list: string list) : Iast.prog_decl list =
  let new_names = List.map (fun c-> (Gen.get_path Sys.executable_name) ^ (String.sub c 1 ((String.length c) - 2))) file_list in
  if (Sys.file_exists "./prelude.ss") then [parse_file_full "./prelude.ss"]
  else List.map parse_file_full new_names

let process_primitives (file_list: string list) : Iast.prog_decl list =
  let pr1 = pr_list (fun x -> x) in
  let pr2 = pr_list (fun x -> (pr_list Iprinter.string_of_rel_decl) x.Iast.prog_rel_decls)  in
  Debug.no_1 "process_primitives" pr1 pr2 process_primitives file_list

(* Process all intermediate primitives which receive after parsing *)
let rec process_intermediate_prims prims_list =
  match prims_list with
  | [] -> []
  | hd::tl ->
        let iprims = Globalvars.trans_global_to_param hd in
        let iprims = Iast.label_procs_prog iprims false in
                iprims :: (process_intermediate_prims tl)

(* Process prelude pragma *)
let rec process_header_with_pragma hlist plist =
  match plist with
  | [] -> hlist
  | hd::tl ->
        let new_hlist = if (hd = "NoImplicitPrelude") then [] else hlist in
            process_header_with_pragma new_hlist tl

(***************end process preclude*********************)

let process_source_full source =
  (* print_string ("\nProcessing file \"" ^ source ^ "\"\n");  *)
  flush stdout;
  let _ = Gen.Profiling.push_time "Preprocessing" in
  let prog = parse_file_full source in
  (* Remove all duplicated declared prelude *)
  let header_files = Gen.BList.remove_dups_eq (=) !Globals.header_file_list in (*prelude.ss*)
  let new_h_files = process_header_with_pragma header_files !Globals.pragma_list in
  let prims_list = process_primitives new_h_files in (*list of primitives in header files*)

  if !to_java then begin
    print_string ("Converting to Java..."); flush stdout;
    let tmp = Filename.chop_extension (Filename.basename source) in
    let main_class = Gen.replace_minus_with_uscore tmp in
    let java_str = Java.convert_to_java prog main_class in
    let tmp2 = Gen.replace_minus_with_uscore (Filename.chop_extension source) in
    let jfile = open_out ("output/" ^ tmp2 ^ ".java") in
    output_string jfile java_str;
    close_out jfile;
    (* print_string (" done-1.\n"); flush stdout; *)
    exit 0
  end;
  if (!Scriptarguments.parse_only) then
    let _ = Gen.Profiling.pop_time "Preprocessing" in
    print_string (Iprinter.string_of_program prog)
  else
    let _ = Tpdispatcher.start_prover () in
    (* Global variables translating *)
    let _ = Gen.Profiling.push_time "Translating global var" in
    let _ = print_string ("Translating global variables to procedure parameters...\n"); flush stdout in

    (* Append all primitives in list into one only *)
    let iprims_list = process_intermediate_prims prims_list in
    let iprims = Iast.append_iprims_list_head iprims_list in
    (* let _ = print_endline ("process_source_full: before Globalvars.trans_global_to_param") in *)
    let intermediate_prog = Globalvars.trans_global_to_param prog in
    (* let _ = print_endline ("process_source_full: before pre_process_of_iprog") in *)
    let intermediate_prog =IastUtil.pre_process_of_iprog iprims intermediate_prog in
    let intermediate_prog = Iast.label_procs_prog intermediate_prog true in
    (* let _ = print_endline ("process_source_full: before --pip") in *)
    let _ = if (!Globals.print_input) then print_string (Iprinter.string_of_program intermediate_prog) else () in
    (* let _ = print_endline ("process_source_full: after --pip") in *)
    let _ = Gen.Profiling.pop_time "Translating global var" in
    (* Global variables translated *)
    (* let ptime1 = Unix.times () in
       let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in *)
    let _ = Gen.Profiling.push_time "Translating to Core" in
    (* let _ = print_string ("Translating to core language...\n"); flush stdout in *)
    let cprog = Astsimp.trans_prog intermediate_prog (*iprims*) in

	(* Forward axioms and relations declarations to SMT solver module *)
	let _ = List.map (fun crdef -> 
        Smtsolver.add_relation crdef.Cast.rel_name crdef.Cast.rel_vars crdef.Cast.rel_formula) (List.rev cprog.Cast.prog_rel_decls) in
	let _ = List.map (fun cadef -> Smtsolver.add_axiom cadef.Cast.axiom_hypothesis Smtsolver.IMPLIES cadef.Cast.axiom_conclusion) (List.rev cprog.Cast.prog_axiom_decls) in
    (* let _ = print_string (" done-2\n"); flush stdout in *)
    let _ = if (!Globals.print_core) then print_string (Cprinter.string_of_program cprog) else () in
    let _ = 
      if !Globals.verify_callees then begin
	    let tmp = Cast.procs_to_verify cprog !Globals.procs_verified in
	    Globals.procs_verified := tmp
      end in
    let _ = Gen.Profiling.pop_time "Translating to Core" in
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
	    print_string ("\nDone-3.\n"); flush stdout;
	    exit 0
      end 
    in
    let _ =
      if !Scriptarguments.rtc then begin
	    Rtc.compile_prog cprog source;
	    exit 0
      end
    in
    let _ = Gen.Profiling.pop_time "Preprocessing" in
    
    (* An Hoa : initialize html *)
    let _ = Prooftracer.initialize_html source in
    
    if (!Scriptarguments.typecheck_only) 
    then print_string (Cprinter.string_of_program cprog)
    else (try
       ignore (Typechecker.check_prog cprog);
    with _ as e -> begin
      print_string ("\nException"^(Printexc.to_string e)^"Occurred!\n");
      print_string ("\nError(s) detected at main "^"\n");
      raise e
    end);
    (* Stopping the prover *)
    let _ = Tpdispatcher.stop_prover () in
    
    (* An Hoa : export the proof to html *)
    let _ = if !Globals.print_proof then
    		begin 
    			print_string "\nExport proof to HTML file ... ";
    			Prooftracer.write_html_output ();
    			print_endline "done!" 
    		end
    in
    
    (* print mapping table control path id and loc *)
    (*let _ = print_endline (Cprinter.string_of_iast_label_table !Globals.iast_label_table) in*)
    
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
	(*;print_string ("\nTotal Entailments : " 
	^ (string_of_int !Globals.total_entailments) ^ "\n" 
	^ "Ramification Entailments : "^ (string_of_int !Globals.ramification_entailments) ^"\n")*)

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
  Scriptarguments.check_option_consistency ();
  if !Globals.print_version_flag then begin
	print_version ()
  end else
  (*let _ = print_endline (string_of_bool (Printexc.backtrace_status())) in*)
    let _ = Printexc.record_backtrace !Globals.trace_failure in
  (*let _ = print_endline (string_of_bool (Printexc.backtrace_status())) in *)

    if List.length (!Globals.source_files) = 0 then begin
      (* print_string (Sys.argv.(0) ^ " -help for usage information\n") *)
      (* Globals.procs_verified := ["f3"]; *)
      (* Globals.source_files := ["examples/test5.ss"] *)
        print_string "Source file(s) not specified\n"
    end;
    let _ = Gen.Profiling.push_time "Overall" in
    let _ = List.map process_source_full !Globals.source_files in
    let _ = Gen.Profiling.pop_time "Overall" in
     (*  Tpdispatcher.print_stats (); *)
      ()

(* let main1 () = *)
(*   Debug.loop_1_no "main1" (fun _ -> "?") (fun _ -> "?") main1 () *)
	  
let finalize () =
  Tpdispatcher.stop_prover ()

let _ = 
  try
    main1 ();
    (* let _ =  *)
    (*   if !Global.enable_counters then *)
    (*     print_string (Gen.Profiling.string_of_counters ()) *)
    (*   else () in *)
    let _ = Gen.Profiling.print_counters_info () in
    let _ = Gen.Profiling.print_info () in
    ()
  with _ as e -> begin
    finalize ();
    print_string "caught\n"; Printexc.print_backtrace stdout;
    print_string ("\nException occurred: " ^ (Printexc.to_string e));
    print_string ("\nError(s) detected at main \n");
  end


  
