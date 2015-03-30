#include "xdebug.cppo"
(******************************************)
(* command line processing                *)
(******************************************)
open Gen.Basic
module M = Lexer.Make(Token.Token)

let to_java = ref false

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let set_source_file arg = 
  Globals.source_files := arg :: !Globals.source_files


let process_cmd_line () = Arg.parse Scriptarguments.sleek_arguments set_source_file usage_msg

(******************************************)
(* main function                          *)
(******************************************)

let parse_file_full file_name = 
  let org_in_chnl = open_in file_name in
  let input = Lexing.from_channel org_in_chnl in
    try
    (*let ptime1 = Unix.times () in
	  let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in
     *)
		print_string "Parsing...\n";
        let () = Gen.Profiling.push_time "Parsing" in
      let prog = Parser.parse_hip file_name (Stream.of_channel org_in_chnl) false in
		(* let prog = Iparser.program (Ilexer.tokenizer file_name) input in *)
		  close_in org_in_chnl;
         let () = Gen.Profiling.pop_time "Parsing" in
    (*		  let ptime2 = Unix.times () in
		  let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
			print_string ("done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n"); *)
			prog 
    with
		End_of_file -> exit 0	  
    | M.Loc.Exc_located (l,t)-> (
        print_string_quiet ((Camlp4.PreCast.Loc.to_string l)^"\n --error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
        raise t
      )

let process_source_full source =
  print_string ("\nProcessing file \"" ^ source ^ "\"\n");
  let () = Gen.Profiling.push_time "Preprocessing" in
  let prog = parse_file_full source in
    if !to_java then begin
      print_string ("Converting to Java...");
      let tmp = Filename.chop_extension (Filename.basename source) in
      let main_class = Gen.replace_minus_with_uscore tmp in
      let java_str = Java.convert_to_java prog main_class in
      let tmp2 = Gen.replace_minus_with_uscore (Filename.chop_extension source) in
      let jfile = open_out ("output/" ^ tmp2 ^ ".java") in
	output_string jfile java_str;
	close_out jfile;
	print_string (" done.\n");
	exit 0
    end;
    if (!Scriptarguments.parse_only) then 
      let () = Gen.Profiling.pop_time "Preprocessing" in
	print_string (Iprinter.string_of_program prog)
    else 

      (* Global variables translating *)
      let () = Gen.Profiling.push_time "Translating global var" in
      let () = print_string ("Translating global variables to procedure parameters...\n"); flush stdout in
      let intermediate_prog = Globalvars.trans_global_to_param prog in
      let intermediate_prog = Iast.label_procs_prog intermediate_prog in
      let () = if (!Globals.print_input) then print_string (Iprinter.string_of_program intermediate_prog) else () in
      let () = Gen.Profiling.pop_time "Translating global var" in
	(* Global variables translated *)
	(* let ptime1 = Unix.times () in
	   let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in *)
      let () = Gen.Profiling.push_time "Translating to Core" in
      let () = print_string ("Translating to core language...\n"); flush stdout in
      let cprog = Astsimp.trans_prog intermediate_prog in
      let () = print_string (" done\n"); flush stdout in
      let () = if (!Globals.print_core || !Globals.print_core_all) then print_string (Cprinter.string_of_program cprog) else () in
      let () = 
	if !Globals.verify_callees then begin
	  let tmp = Cast.procs_to_verify cprog !Globals.procs_verified in
	    Globals.procs_verified := tmp
	end in
      let () = Gen.Profiling.pop_time "Translating to Core" in
	(* let ptime2 = Unix.times () in
	   let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
	   let () = print_string (" done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n") in *)
      let _ =
	if !Scriptarguments.comp_pred then begin
	  let () = print_string ("Compiling predicates to Java...") in
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
	    print_string ("\nDone.\n");
	    exit 0
	end 
      in
      let _ =
	if !Scriptarguments.rtc then begin
	  Rtc.compile_prog cprog source;
	  exit 0
	end
      in
      let () = Gen.Profiling.pop_time "Preprocessing" in
	if !Gui.enable_gui then begin
	  ignore (Gui.check_prog (Gui.get_win ()) cprog)
	end
	else 
	  ignore (Typechecker.check_prog cprog);

	(* i.e. stop Reduce/Redlog if it is running. *)
	let () = Tpdispatcher.finalize () in

	let ptime4 = Unix.times () in
	let t4 = ptime4.Unix.tms_utime +. ptime4.Unix.tms_cutime +. ptime4.Unix.tms_stime +. ptime4.Unix.tms_cstime   in
	  print_string ("\n"^(string_of_int (List.length !Globals.false_ctx_line_list))^" false contexts at: ("^
			  (List.fold_left (fun a c-> a^" ("^(string_of_int c.VarGen.start_pos.Lexing.pos_lnum)^","^
					     ( string_of_int (c.VarGen.start_pos.Lexing.pos_cnum-c.VarGen.start_pos.Lexing.pos_bol))^") ") "" !Globals.false_ctx_line_list)^")\n");
	  print_string ("\nTotal verification time: " 
			^ (string_of_float t4) ^ " second(s)\n"
			^ "\tTime spent in main process: " 
			^ (string_of_float (ptime4.Unix.tms_utime+.ptime4.Unix.tms_stime)) ^ " second(s)\n"
			^ "\tTime spent in child processes: " 
			^ (string_of_float (ptime4.Unix.tms_cutime +. ptime4.Unix.tms_cstime)) ^ " second(s)\n")



let main_gui () = 
  (* process_cmd_line (); *)
  let () = GMain.init () in
  let () = Tpdispatcher.prepare () in
    if List.length (!Globals.source_files) = 0 then begin
      (* print_string (Sys.argv.(0) ^ " -help for usage information\n") *)
      (* Globals.procs_verified := ["f3"]; *)
      (* Globals.source_files := ["examples/test5.ss"] *)
        print_string "Source file(s) not specified\n"
    end;
    let () = Gui.set_win (new Gui.mainwindow "HIP VIEWER" (List.hd !Globals.source_files)) in 
      Gen.Profiling.push_time "Overall";
      ignore (List.map process_source_full !Globals.source_files);
      Gen.Profiling.pop_time "Overall";
      (Gui.get_win ())#show ();
      GMain.Main.main ()



	  
let main1 () =
  (* process_cmd_line (); *)
  
  (* i.e. pre-start Reduce/Redlog if it will be used. *)
  let () = Tpdispatcher.prepare () in
  
  if List.length (!Globals.source_files) = 0 then begin
	(* print_string (Sys.argv.(0) ^ " -help for usage information\n") *)
	(* Globals.procs_verified := ["f3"]; *)
	(* Globals.source_files := ["examples/test5.ss"] *)
      print_string "Source file(s) not specified\n"
  end;
  let () = Gen.Profiling.push_time "Overall" in
  let todo_unk = List.map process_source_full !Globals.source_files in
  let () = Gen.Profiling.pop_time "Overall" in
	(* Tpdispatcher.print_stats (); *)
	()
	  
let () =  
  process_cmd_line ();
  let () = Debug.read_main () in
  if !Gui.enable_gui then main_gui () 
  else 
    main1 ();
  (*let rec check_aux (t1,t2,t3,t4) l = match l with
    | [] -> true
    | (p1,p2,p3,p4)::l1 -> if (p1<=t1 && p2<=t2&& p3<=t3&& p4<=t4) then check_aux (p1,p2,p3,p4) l1
    else false in
    let check_sorted l = match l with
    | a::b -> check_aux a b
    | [] -> true  in
    let () = print_string ("stack height: "^(string_of_int (List.length !Util.profiling_stack))^"\n") in
    let () = print_string ("get time length: "^(string_of_int (List.length !Util.time_list))^" "^
    (string_of_bool (check_sorted !Util.time_list))^"\n" ) in*)
  let () = print_string (Gen.Profiling.string_of_counters ()) in
  let () = Gen.Profiling.print_info () in
  ()
  
