
module ViewNode = struct
  type t = string
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module G = Graph.Imperative.Digraph.Concrete(ViewNode)
module TG = Graph.Topological.Make(G)
module CG = Graph.Traverse.Dfs(G)

open G

let edges = [("d", "c"); ("a", "b"); ("b", "c"); ("a", "d"); ("e", "b"); ("b", "e")]
(*let edges = [(1,2);(3,4);(1,3)]*)

let g = create ()

let _ =
  print_string ("testing ocamlgraph\n");
  ignore (List.map (fun (v1, v2) -> add_edge g (V.create v1) (V.create v2)) edges);
  TG.iter (fun s -> print_string (s ^ "\n")) g;
  if CG.has_cycle g then
	print_string ("g has cycle\n")
  else
	print_string ("acylic\n")
