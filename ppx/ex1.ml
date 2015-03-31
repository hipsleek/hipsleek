type point2d = float * float
[@@deriving show]

let x = (2.0,3.0);;

print_endline (show_point2d x);;

(* ocamlfind ocamlc -package ppx_deriving.std -o ex1 ppx/ex1.ml *)
