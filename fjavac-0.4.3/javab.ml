(* javab.ml - java parser *)

let main fs : unit =
  let cs = Listx.map Jparse.parse fs in
  if Util.arg_bool "-sexp" then         (* print as s-exp *)
    Std.printl (Listx.show2 Jsyntax.cunit_sexp cs);
  if Util.arg_bool "-src" then         (* print as source *)
    Std.printl (Listx.show2 Jsyntax.cunit_src cs);
  if Util.arg_bool "-tag" then         (* print as tag *)
    Std.printl (Listx.show2 Jsyntax.cunit_tag cs)

let _ = main (Util.arg_list ())
