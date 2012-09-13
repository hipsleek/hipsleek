open Mainutil


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


let pre_main =
  process_cmd_line ();
  Scriptarguments.check_option_consistency ();
  if !Globals.print_version_flag then
	  let _ = print_version ()
    in []
  else
    let _ = Printexc.record_backtrace !Globals.trace_failure in
    if List.length (!Globals.source_files) = 0 then
      print_string "Source file(s) not specified\n";
    List.map process_source_full_parse_only !Globals.source_files

let loop_cmd parsed_content = 
  let _ = List.map2 (fun s t -> process_source_full_after_parser s t) !Globals.source_files parsed_content in
  ()

let old_main =
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


let _ =
  if not(!Globals.do_infer_inc) then old_main
  else
    let res = pre_main in
    while true do
      try
        let _ = print_string "# " in
        let s = Parse_cmd.parse_cmd (read_line ()) in
        match s with
          | (_,(false, None, None)) -> exit 0;
          | _ ->
          Iformula.cmd := s;
          loop_cmd res;
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
    done


  
