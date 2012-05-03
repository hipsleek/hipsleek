ocamlopt -c -I cil/cil-1.4.0/obj/x86_LINUX/ cilhip.ml
ocamlopt -ccopt -Lcil/cil-1.4.0/obj/x86_LINUX/ -o cilhip unix.cmxa str.cmxa cil/cil-1.4.0/obj/x86_LINUX/cil.cmxa cilhip.cmx
