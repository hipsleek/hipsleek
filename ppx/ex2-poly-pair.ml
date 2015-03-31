
type ('a,'b) pair = 'a * b
[@@deriving show]

type point2d = (float,float) pair
[@@deriving show]

let x = (2.0,3.0);;

print_endline (show_point2d x);;

(* ocamlfind ocamlc -package ppx_deriving.std -o ex1 ppx/ex1.ml *)
