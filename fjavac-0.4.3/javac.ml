(* javac.ml - java compiler *)

let main (fs:string list) : unit =
  let t1 = Listx.map Jparse.parse fs in
  if Util.arg_bool "-vv" then (
    Std.printl "\n---- plain syntax tree as s-expression";
    Std.printl (Listx.show2 Jsyntax.cunit_sexp t1));
  if Util.arg_bool "-po" then exit 0;    (* parse only *)

  let t2 = Jplain.ctask_of t1 in
  if Util.arg_bool "-v" then (
    Std.printl "\n---- plain syntax tree";
    Std.printl (Jplain.ctask_show t2));
  if Util.arg_bool "-no" then exit 0;    (* normalize only *)

  let t3 = Jtyping.ctask_of t2 in
  if Util.arg_bool "-v" then (
    Std.printl "\n---- typed syntax tree";
    Std.printl (Jtyped.ctask_show t3));
  if Util.arg_bool "-to" then exit 0;    (* type-check only *)

  let t4 = Jasm.ctask_of t3 in
  if Util.arg_bool "-v" then (
    Std.printl "\n---- classfile assembly";
    Std.printl (Listx.show2 Jasm.cfile_show t4));
  if Util.arg_bool "-co" then exit 0;    (* compile only *)

  let t5 = Jbytecode.ctask_of t4 in
  if Util.arg_bool "-v" then (
    Std.printl "\n---- classfile bytecode";
    Std.printl (Listx.show2 Jbytecode.cfile_show t5));

  Listx.iter Jbyteio.write t5

let _ = main (Util.arg_list ())


(* 

1. concrete syntax grammar (java.g)
2. concrete syntax tree (jsyntax.g)
3. abstract plain syntax tree (jplain.g)
4. abstract typed syntax tree (jtyped.g)
5. abstract assembly bytecode (jasm.g)
6. concrete classfile bytecode (jbytecode.g)

*)
