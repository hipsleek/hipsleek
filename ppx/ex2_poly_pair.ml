
type ('a,'b) pair = 'a * 'b
[@@deriving show]

type point2d = (float,float) pair
[@@deriving show]

let x = (2.0,3.0);;

type point2d_list = point2d list
[@@deriving show]

let ls = [x;x;x;x;x;x;x;x;x;x;x];;

type 'a tree = Empty | Node of 'a * ('a tree) * ('a tree)
[@@deriving show]

type tree_f = point2d tree
[@@deriving show]

let t1 = Node(x,Empty,Empty);;
let t2 = Node(x,t1,t1);;
let t3 = Node(x,t2,t2);;
let t4 = Node(x,t3,t3);;
let t5 = Node(x,t3,t4);;


print_endline (show_point2d x);;

print_endline (show_point2d_list ls);;


print_endline (show_tree_f t1);;
print_endline (show_tree_f t2);;
print_endline (show_tree_f t3);;
print_endline (show_tree_f t4);;
print_endline (show_tree_f t5);;

print_endline (show_tree pp_point2d t1);;

(* ocamlfind ocamlc -package ppx_deriving.std -c ex2 ppx/ex2_poly_pair.ml *)
