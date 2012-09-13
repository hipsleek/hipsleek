open Gsmainform
open GUtil

(**********************
 * MAIN FUNCTION
 **********************)
let usage_msg = Sys.argv.(0) ^ " [options] <source file>"
let arguments = [
  ("-v", Arg.Set verbose_flag, "Verbose")
  ]

let _ =
  GUtil.initialize ();
  let win = new mainwindow () in
  Arg.parse arguments win#open_file usage_msg;
  win#show ();
  GMain.Main.main ();
  Mainutil.finalize ()

