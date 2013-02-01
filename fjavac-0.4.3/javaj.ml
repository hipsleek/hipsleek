(* -*- compile-command: "make javaj" -*- *)
(* javaj.ml - java jar *)

open Std
module J = Jjar
module T = Jtyped


let main j : string list -> unit = function
  | (["field";c;x]) -> printl (T.fty_show (J.field j (T.cname_read c) x))
  | (["kind";c]) -> printl (T.ckind_show (J.kind j (J.cname_of j (Jplain.name_read c))))
  | (["class";c]) -> printl (T.cname_showx (J.cname_of j (Jplain.name_read c)))
  | (["methods";c;x]) -> 
    printl (Listx.show1 T.mty_showx (J.methods j (J.cname_of j (Jplain.name_read c)) x))
  | (["cnames";c]) -> 
    printl (Listx.show1 T.cname_showx (J.cnames j (Jplain.name_read c) []))
  | (["ifaces";c]) -> 
    printl (Listx.show1 T.cname_show (J.ifaces j (T.cname_read c)))
  | _ -> printl "unknown command"

let _ = main (J.load "rt.jar") (Listx.skip 1 (Arrayx.to_list Sys.argv))
