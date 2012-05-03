
(*
ocamlopt -c -I cil-1.3.7/obj/x86_LINUX/ main.ml
ocamlopt -ccopt -Lcil-1.3.7/obj/x86_LINUX/ -o main unix.cmxa str.cmxa cil-1.3.7/obj/x86_LINUX/cil.cmxa main.cmx
./main > output.c

let _ = 
  let cil = Frontc.parse "input.c" () in
  let _ = Rmtmps.removeUnusedTemps cil in
  Cil.lineDirectiveStyle := None;
  Cprint.printLn := false;
  Cil.dumpFile Cil.defaultCilPrinter stdout "output.cil" cil 
*)
