(**
  GUI frontend for HIP
 *)

open Globals
open GUtil
open Gen
open Ghmainform

module MU = Mainutil

(**********************
 * MAIN FUNCTION
 **********************)
let usage_msg = Sys.argv.(0) ^ " [options] <source file>"
let arguments = [
  ("-v", Arg.Set verbose_flag, "Verbose")
  ]

let _ =
  (* GUtil.initialize (); *)
  (* reporter:= (fun loc msg -> *)
  (*   let pos = { *)
  (*     SourceUtil.start_char = loc.start_pos.Lexing.pos_cnum; *)
  (*     SourceUtil.stop_char = loc.end_pos.Lexing.pos_cnum; *)
  (*     SourceUtil.start_line = loc.start_pos.Lexing.pos_lnum; *)
  (*     SourceUtil.stop_line = loc.end_pos.Lexing.pos_lnum; *)
  (*   } in *)
  (*   raise (SourceUtil.Syntax_error ("Syntax error: " ^ msg, pos)) *)
  (* ); *)
  ignore (GtkMain.Main.init ());
  let win = new mainwindow () in
  MU.process_cmd_line ();
  Scriptarguments.check_option_consistency ();
  let _ = Printexc.record_backtrace !Globals.trace_failure in
  if List.length (!Globals.source_files) = 0 then
    print_string "Source file(s) not specified\n";
 
  (* Arg.parse arguments  win#open_file usage_msg *) win#open_file (List.hd !Globals.source_files);
  win#show ();
  GMain.Main.main ();
  Mainutil.finalize ();
  print_string  "\n";

