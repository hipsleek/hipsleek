open Globals
open Gen

let rec partition_by_assoc eq ls =
  match ls with
  | [] -> []
  | ((k, _) as x)::xs -> 
    let k_xs, nk_xs = List.partition (fun (ks, _) -> eq k ks) xs in
    (x::k_xs)::(partition_by_assoc eq nk_xs)

