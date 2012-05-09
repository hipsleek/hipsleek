
(*
ocamlopt -c -I cil-1.3.7/obj/x86_LINUX/ main.ml
ocamlopt -ccopt -Lcil-1.3.7/obj/x86_LINUX/ -o main unix.cmxa str.cmxa cil-1.3.7/obj/x86_LINUX/cil.cmxa main.cmx
./main > output.c
*)

open Frontc

let _ = 
  let cil = Frontc.parse "input.c" () in
  let _ = Rmtmps.removeUnusedTemps cil in
  Cil.lineDirectiveStyle := None;
  Cprint.printLn := false;

  (* use default printer *)
  let _ = print_endline "----- default cil printer -----" in
  Cil.dumpFile (new Cil.defaultCilPrinterClass) stdout "output.cil" cil;

  (* use hip printer *)
  let _ = print_endline "\n\n----- hip cil printer -----" in
  Cil.dumpFile (new Pcilhip.hipVisitor) stdout "output.cil" cil;
